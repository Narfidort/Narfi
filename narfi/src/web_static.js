// Narfi Web 版（サーバーなし）：/api/… への要求を、ブラウザの中の WebAssembly と保存領域で処理する。
//
// ローカル版（narfi web）から開いたときは、サーバーが window.NARFI_LOCAL = true を埋め込むので何もしない。
// Web 版（Cloudflare Pages などの静的な置き場所）から開いたときだけ、fetch を差し替える。
//
// - 検査器：narfi.wasm（src/wasm.rs）。要求・応答は JSON で、/api/check・/api/convert と同じ形
// - ファイル：localStorage の "narfi.fs.v1"（パス → 中身）。この PC のこのブラウザの中だけに残る
// - 読み込み：Open（.narfi ファイル）・Folder（フォルダごと）、書き出し：Finder（全ファイルを zip）

(function () {
  if (window.NARFI_LOCAL) return;
  window.NARFI_WEB = true;

  const FS_KEY = "narfi.fs.v1";
  const enc = new TextEncoder();
  const dec = new TextDecoder();

  // ---------------------------------------------------------------- 保存領域

  function loadFs() {
    try { return JSON.parse(localStorage.getItem(FS_KEY) || "{}"); } catch (_) { return {}; }
  }
  function saveFs(fs) {
    localStorage.setItem(FS_KEY, JSON.stringify(fs));
  }

  // ---------------------------------------------------------------- WebAssembly

  let wasm = null;
  async function instantiate() {
    const resp = await realFetch("/narfi.wasm");
    const bytes = await resp.arrayBuffer();
    const { instance } = await WebAssembly.instantiate(bytes, {});
    wasm = instance.exports;
    // 保存領域のファイルを検査器に知らせる（import できるように）
    const fs = loadFs();
    for (const [path, src] of Object.entries(fs)) call({ op: "put_file", path, src });
  }

  function call(req) {
    const b = enc.encode(JSON.stringify(req));
    const p = wasm.narfi_alloc(b.length);
    new Uint8Array(wasm.memory.buffer, p, b.length).set(b);
    let n;
    try {
      n = wasm.narfi_call(p, b.length);
    } catch (e) {
      // 検査器の中で止まった（桁あふれなど）。作り直して、この要求はエラーとして返す
      ready = instantiate();
      throw e;
    }
    wasm.narfi_free(p, b.length);
    return JSON.parse(dec.decode(new Uint8Array(wasm.memory.buffer, wasm.narfi_out_ptr(), n)));
  }

  const realFetch = window.fetch.bind(window);
  let ready = instantiate();

  function json(obj, status = 200) {
    return new Response(JSON.stringify(obj), { status, headers: { "Content-Type": "application/json" } });
  }

  function bodyOf(opts) {
    try { return JSON.parse((opts && opts.body) || "{}"); } catch (_) { return {}; }
  }

  // ---------------------------------------------------------------- ファイルを選ぶ・書き出す

  function pickFiles({ directory }) {
    return new Promise((resolve) => {
      const input = document.createElement("input");
      input.type = "file";
      if (directory) input.webkitdirectory = true;
      else input.accept = ".narfi,.txt,text/plain";
      input.multiple = !!directory;
      input.addEventListener("change", () => resolve([...input.files]));
      input.addEventListener("cancel", () => resolve([]));
      input.click();
    });
  }

  function download(name, blob) {
    const a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = name;
    document.body.appendChild(a);
    a.click();
    setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
  }

  // 無圧縮の zip（外部ライブラリなし）
  const CRC = (() => {
    const t = new Uint32Array(256);
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
      t[n] = c >>> 0;
    }
    return t;
  })();
  function crc32(bytes) {
    let c = 0xffffffff;
    for (const b of bytes) c = CRC[(c ^ b) & 0xff] ^ (c >>> 8);
    return (c ^ 0xffffffff) >>> 0;
  }
  function zip(files) {
    const parts = [];
    const central = [];
    let offset = 0;
    const u16 = (v) => [v & 0xff, (v >>> 8) & 0xff];
    const u32 = (v) => [v & 0xff, (v >>> 8) & 0xff, (v >>> 16) & 0xff, (v >>> 24) & 0xff];
    for (const [name, text] of files) {
      const nb = enc.encode(name);
      const data = enc.encode(text);
      const crc = crc32(data);
      // 汎用ビット 11（0x0800）：ファイル名は UTF-8
      const local = [...u32(0x04034b50), ...u16(20), ...u16(0x0800), ...u16(0), ...u16(0), ...u16(0),
        ...u32(crc), ...u32(data.length), ...u32(data.length), ...u16(nb.length), ...u16(0)];
      parts.push(new Uint8Array(local), nb, data);
      central.push(new Uint8Array([...u32(0x02014b50), ...u16(20), ...u16(20), ...u16(0x0800), ...u16(0), ...u16(0), ...u16(0),
        ...u32(crc), ...u32(data.length), ...u32(data.length), ...u16(nb.length), ...u16(0), ...u16(0), ...u16(0), ...u16(0),
        ...u32(0), ...u32(offset)]), nb);
      offset += local.length + nb.length + data.length;
    }
    const csize = central.reduce((s, a) => s + a.length, 0);
    const end = new Uint8Array([...u32(0x06054b50), ...u16(0), ...u16(0), ...u16(files.length), ...u16(files.length),
      ...u32(csize), ...u32(offset), ...u16(0)]);
    return new Blob([...parts, ...central, end], { type: "application/zip" });
  }

  // ---------------------------------------------------------------- /api/… の処理

  function workspace() {
    const fs = loadFs();
    const std = call({ op: "stdlib_list" }).files || [];
    return {
      ok: true,
      web: true,
      root: "ブラウザ内の保存領域",
      name: "このブラウザ",
      files: Object.keys(fs).sort(),
      libs: [{ label: "std", dir: "", files: std }],
      dialogs: true
    };
  }

  function storeFile(path, src) {
    const fs = loadFs();
    fs[path] = src;
    saveFs(fs);
    call({ op: "put_file", path, src });
  }

  async function handle(path, query, opts) {
    await ready;
    const body = bodyOf(opts);
    switch (path) {
      case "/api/check":
        return json(call({ op: "check", src: body.src || "", path: body.path && !body.path.startsWith("lib:") ? body.path : "", cursor_line: body.cursor_line || 0 }));
      case "/api/convert":
        return json(call({ op: "convert", src: body.src || "", mode: body.mode || "" }));
      case "/api/workspace":
        return json(workspace());
      case "/api/file": {
        const p = query.get("path") || "";
        if (p.startsWith("lib:std/")) {
          const r = call({ op: "stdlib_get", path: p.slice("lib:std/".length) });
          return json(r.ok ? { ok: true, path: p, src: r.src } : { ok: false, error: "ない" });
        }
        const fs = loadFs();
        return json(p in fs ? { ok: true, path: p, src: fs[p] } : { ok: false, error: `${p} がない` });
      }
      case "/api/save": {
        if (!body.path || body.path.startsWith("lib:")) return json({ ok: false, error: "保存先が正しくない" });
        storeFile(body.path, body.src || "");
        return json({ ok: true, path: body.path });
      }
      case "/api/save-as": {
        let name = prompt("ブラウザ内に保存する名前（フォルダは / で区切る）:", body.name || "note.narfi");
        if (!name) return json({ ok: false, cancelled: true });
        name = name.replace(/^\/+/, "");
        if (!name.endsWith(".narfi")) name += ".narfi";
        if (name in loadFs() && !confirm(`${name} はすでにある。上書きしてよいですか？`)) return json({ ok: false, cancelled: true });
        storeFile(name, body.src || "");
        return json({ ok: true, path: name, src: body.src || "" });
      }
      case "/api/open-file": {
        const files = await pickFiles({ directory: false });
        if (files.length === 0) return json({ ok: false, cancelled: true });
        const f = files[0];
        const src = await f.text();
        if (f.name in loadFs() && !confirm(`ブラウザ内の ${f.name} を、読み込んだファイルで上書きしてよいですか？`)) {
          return json({ ok: false, cancelled: true });
        }
        storeFile(f.name, src);
        return json({ ok: true, path: f.name, src });
      }
      case "/api/open-folder": {
        // フォルダの中の .narfi をまとめて読み込む（フォルダの名前は外し、中の構成は保つ）
        const files = (await pickFiles({ directory: true })).filter((f) => f.name.endsWith(".narfi"));
        if (files.length === 0) return json({ ok: false, cancelled: true });
        for (const f of files) {
          const rel = (f.webkitRelativePath || f.name).split("/").slice(1).join("/") || f.name;
          storeFile(rel, await f.text());
        }
        return json(workspace());
      }
      case "/api/reveal": {
        const fs = loadFs();
        if (body.target === "lib") {
          alert("Web 版では、自分用のライブラリは保存領域の lib/ フォルダに置く（例：lib/mydefs.narfi は import mydefs で読める）。");
        } else if (Object.keys(fs).length === 0) {
          alert("ブラウザ内にファイルがない");
        } else {
          const stamp = new Date().toISOString().slice(0, 10);
          download(`narfi-${stamp}.zip`, zip(Object.entries(fs)));
        }
        return json({ ok: true });
      }
      case "/api/pdf":
        return json({ ok: false, error: "Web 版では LaTeX の PDF は作れない。Print（⌘P）から「PDF として保存」を使う。" }, 400);
      case "/api/ai":
      case "/api/ai/providers":
        return json({ ok: false, error: "Web 版では AI 補助は使えない（ローカル版の narfi web で使える）" });
      default:
        return json({ ok: false, error: `Web 版にない API: ${path}` }, 404);
    }
  }

  window.fetch = async (input, opts) => {
    const url = typeof input === "string" ? input : input.url;
    const u = new URL(url, location.href);
    if (u.origin === location.origin && u.pathname.startsWith("/api/")) {
      try {
        return await handle(u.pathname, u.searchParams, opts);
      } catch (e) {
        return json({ ok: false, error: `検査器のエラー: ${e}` }, 500);
      }
    }
    return realFetch(input, opts);
  };

  // ボタンの名前を Web 版に合わせる
  window.addEventListener("DOMContentLoaded", () => {
    const set = (sel, text, title) => {
      for (const b of document.querySelectorAll(sel)) {
        b.textContent = text;
        if (title) b.title = title;
      }
    };
    set('button[onclick="openFolder()"]', "Import", "フォルダの中の .narfi をまとめてブラウザ内に読み込む");
    set('button[onclick="revealDir(\'workspace\')"]', "Export", "ブラウザ内の全ファイルを zip で書き出す（バックアップ・持ち出し用）");
    set('button[onclick="revealDir(\'lib\')"]', "lib/ について");
    set('button[onclick="openFileDialog()"]', "Open", "パソコンの .narfi ファイルをブラウザ内に読み込む（⌘O）");
    set('button[onclick="exportPdf()"]', "PDF", "Web 版では使えない。Print から「PDF として保存」を使う");
  });
})();
