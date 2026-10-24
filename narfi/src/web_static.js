// Narfi Web 版（サーバーなし）：/api/… への要求を、ブラウザの中の WebAssembly と保存領域で処理する。
//
// ローカル版（narfi web）から開いたときは、サーバーが window.NARFI_LOCAL = true を埋め込むので何もしない。
// Web 版（Cloudflare Pages などの静的な置き場所）から開いたときだけ、fetch を差し替える。
//
// - 検査器：narfi.wasm（src/wasm.rs）。要求・応答は JSON で、/api/check・/api/convert と同じ形
// - ファイル：localStorage の "narfi.fs.v1"（パス → 中身）。この PC のこのブラウザの中だけに残る
// - 読み込み：Open（.narfi ファイル）・Folder（フォルダごと）、書き出し：Finder（全ファイルを zip）
// - クラウド保存：GitHub でログインすると、保存領域を Cloudflare D1 と同期する（functions/・server/common.js）。
//   手元の保存領域がいつも本体で、変更は後からクラウドへ送る（つながらない間も使える）

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
  let wasmTag = null;
  async function instantiate() {
    const resp = await realFetch("/narfi.wasm");
    wasmTag = resp.headers.get("etag");
    const bytes = await resp.arrayBuffer();
    const { instance } = await WebAssembly.instantiate(bytes, {});
    wasm = instance.exports;
    // 保存領域のファイルを検査器に知らせる（import できるように）
    const fs = loadFs();
    for (const [path, src] of Object.entries(fs)) call({ op: "put_file", path, src });
  }

  // 新しい版が出たら知らせる（開いたままのタブは古い検査器のままなので）
  let updateShown = false;
  async function checkUpdate() {
    if (updateShown || !wasmTag) return;
    try {
      const r = await realFetch("/narfi.wasm", { method: "HEAD", cache: "no-store" });
      const tag = r.headers.get("etag");
      if (!tag || tag === wasmTag) return;
      updateShown = true;
      const bar = document.createElement("div");
      bar.style.cssText = "position:fixed;left:50%;bottom:36px;transform:translateX(-50%);z-index:9999;background:#1f6feb;color:#fff;padding:8px 14px;border-radius:8px;font:13px -apple-system,sans-serif;box-shadow:0 4px 16px rgba(0,0,0,.35)";
      bar.innerHTML = 'Narfi の新しい版があります。 <button style="margin-left:8px;border:0;border-radius:5px;padding:3px 10px;cursor:pointer">再読み込み</button>';
      bar.querySelector("button").onclick = () => location.reload();
      document.body.appendChild(bar);
    } catch (_) {}
  }
  document.addEventListener("visibilitychange", () => { if (document.visibilityState === "visible") checkUpdate(); });
  setInterval(checkUpdate, 10 * 60 * 1000);

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

  // ---------------------------------------------------------------- クラウド保存（GitHub でログイン）
  //
  // 同期の記録（"narfi.sync.v1"）：
  //   user  … 同期している GitHub のアカウントの ID
  //   base  … パス → 最後に同期したときのクラウドの version
  //   dirty … クラウドにまだ送っていない、手元で変えたパス
  // 手元とクラウドの両方で変わっていたら、手元のものをそのパスに残し、クラウドのものは「名前.conflict-日時.narfi」として残す。

  const SYNC_KEY = "narfi.sync.v1";
  const cloud = { configured: false, user: null, state: "off", busy: null, again: false, timer: null, error: "", conflicts: [] };

  function loadSync() {
    try {
      const m = JSON.parse(localStorage.getItem(SYNC_KEY) || "null");
      if (m && typeof m === "object") return { user: m.user || null, base: m.base || {}, dirty: m.dirty || [], deleted: m.deleted || {} };
    } catch (_) {}
    return { user: null, base: {}, dirty: [], deleted: {} };
  }
  function saveSync(m) {
    localStorage.setItem(SYNC_KEY, JSON.stringify(m));
  }

  async function cloudFetch(path, opts = {}) {
    const headers = { "X-Narfi-Cloud": "1", ...(opts.body ? { "Content-Type": "application/json" } : {}) };
    const r = await realFetch(path, { credentials: "same-origin", cache: "no-store", ...opts, headers });
    let data = {};
    try { data = await r.json(); } catch (_) { data = { ok: false, error: "応答が JSON でない" }; }
    data.status = r.status;
    return data;
  }

  function cloudNoteLocalChange(path) {
    if (!cloud.user) return;
    const m = loadSync();
    if (!m.dirty.includes(path)) m.dirty.push(path);
    saveSync(m);
    scheduleSync(800);
  }

  // 手元で消した（名前を変えた）ファイル：クラウドからも消す
  function cloudNoteDelete(path) {
    if (!cloud.user) return;
    const m = loadSync();
    if (m.base[path] !== undefined) m.deleted[path] = m.base[path];
    delete m.base[path];
    m.dirty = m.dirty.filter((p) => p !== path);
    saveSync(m);
    scheduleSync(800);
  }

  function removeLocal(path) {
    const fs = loadFs();
    delete fs[path];
    saveFs(fs);
    call({ op: "remove_file", path });
  }

  function scheduleSync(ms) {
    if (!cloud.user) return;
    if (cloud.timer) clearTimeout(cloud.timer);
    cloud.timer = setTimeout(() => { cloud.timer = null; syncNow(); }, ms);
  }

  function conflictName(path) {
    const d = new Date();
    const p2 = (n) => String(n).padStart(2, "0");
    const stamp = `${d.getFullYear()}${p2(d.getMonth() + 1)}${p2(d.getDate())}-${p2(d.getHours())}${p2(d.getMinutes())}`;
    return path.replace(/\.narfi$/, "") + `.conflict-${stamp}.narfi`;
  }

  // 手元のファイルを置き換える（クラウドから来たもの）。dirty にはしない
  function putLocal(path, src) {
    const fs = loadFs();
    fs[path] = src;
    saveFs(fs);
    call({ op: "put_file", path, src });
  }

  async function push(m, fs, path) {
    const src = fs[path];
    const r = await cloudFetch("/cloud/file", { method: "PUT", body: JSON.stringify({ path, src, base: m.base[path] || 0 }) });
    if (r.ok) {
      m.base[path] = r.version;
      if (loadFs()[path] === src) m.dirty = m.dirty.filter((p) => p !== path);
      return true;
    }
    if (r.status === 409) return false;
    throw new Error(r.error || `保存できなかった（${r.status}）`);
  }

  // 1 回の同期：クラウドの一覧と手元を比べ、取ってくる・送る
  async function syncOnce() {
    // 手元で消したものを、クラウドからも消す（その間にほかの端末で変えられていたら、消さずに取ってくる）
    for (const [path, base] of Object.entries(loadSync().deleted)) {
      const r = await cloudFetch(`/cloud/file?path=${encodeURIComponent(path)}&base=${base}`, { method: "DELETE" });
      if (!r.ok && r.status !== 409 && r.status !== 400) throw new Error(r.error || `消せなかった（${r.status}）`);
      const m1 = loadSync();
      delete m1.deleted[path];
      saveSync(m1);
    }
    const list = await cloudFetch("/cloud/files");
    if (list.status === 401) { signedOut(); return []; }
    if (!list.ok) throw new Error(list.error || "一覧が取れなかった");
    const m = loadSync();
    const changed = [];
    const remote = new Map(list.files.map((f) => [f.path, f.version]));
    let fs = loadFs();
    const handled = new Set();
    for (const [path, version] of remote) {
      const local = fs[path];
      const base = m.base[path];
      const dirty = m.dirty.includes(path);
      if (base === version && !dirty) continue;
      if (base === version && dirty) {
        handled.add(path);
        if (!(await push(m, fs, path))) cloud.again = true;
        continue;
      }
      // クラウドで変わっている（または初めて同期する）
      const r = await cloudFetch(`/cloud/file?path=${encodeURIComponent(path)}`);
      if (!r.ok) continue;
      if (local === undefined || local === r.src || (!dirty && base !== undefined)) {
        if (local !== r.src) { putLocal(path, r.src); changed.push(path); }
        m.base[path] = r.version;
        m.dirty = m.dirty.filter((p) => p !== path);
      } else {
        // 両方で変わった：クラウドのものを別の名前で残し、手元のものを送る
        const other = conflictName(path);
        putLocal(other, r.src);
        cloud.conflicts.push([path, other]);
        m.dirty.push(other);
        changed.push(other);
        m.base[path] = r.version;
        if (!m.dirty.includes(path)) m.dirty.push(path);
      }
      fs = loadFs();
    }
    // 手元にだけあるもの・手元で変えたもの
    for (const path of Object.keys(fs)) {
      if (handled.has(path) || (remote.has(path) && !m.dirty.includes(path))) continue;
      if (!remote.has(path)) {
        // 前に同期したのにクラウドにない：ほかの端末で消された。手元で変えていなければ手元も消す
        if (m.base[path] !== undefined && !m.dirty.includes(path)) {
          removeLocal(path);
          delete m.base[path];
          changed.push(path);
          continue;
        }
        delete m.base[path];
      }
      if (!(await push(m, fs, path))) cloud.again = true;
    }
    saveSync(m);
    return changed;
  }

  async function syncNow() {
    if (!cloud.user) return;
    if (cloud.busy) { cloud.again = true; return cloud.busy; }
    cloud.busy = (async () => {
      setCloudState("syncing");
      const changed = [];
      try {
        for (let k = 0; k < 3; k++) {
          cloud.again = false;
          changed.push(...(await syncOnce()));
          if (!cloud.again) break;
        }
        if (cloud.user) setCloudState(loadSync().dirty.length ? "pending" : "synced");
      } catch (e) {
        cloud.error = String(e.message || e);
        setCloudState(navigator.onLine === false ? "offline" : "error");
      } finally {
        cloud.busy = null;
      }
      if (changed.length) window.dispatchEvent(new CustomEvent("narfi:files-changed", { detail: { paths: changed } }));
      if (cloud.conflicts.length) {
        const list = cloud.conflicts.map(([p, o]) => `${p} → ${o}`).join("\n");
        cloud.conflicts = [];
        setTimeout(() => window.uiToast(`ほかの端末でも同じファイルが変更されていたため、そちらの版を別の名前で残しました：${list.replace(/\n/g, "、")}`), 0);
      }
    })();
    return cloud.busy;
  }

  function signedOut() {
    cloud.user = null;
    setCloudState("signed-out");
  }

  async function cloudInit() {
    const me = await cloudFetch("/cloud/me").catch(() => ({ ok: false }));
    cloud.configured = !!me.configured;
    if (!cloud.configured) { setCloudState("off"); return; }
    if (!me.signed_in) {
      signedOut();
      // Web 版はログインして使う（ファイルはアカウントに保存される）。閉じられない画面
      await window.uiModal({
        title: "Narfi へようこそ",
        note: "GitHub のアカウントでログインして使います。ファイルはアカウントに保存され、ほかの PC やブラウザでも開けます（ログインしたままになります）。GitHub に求める権限はありません（公開プロフィールの ID と名前だけを使います）。",
        okLabel: "GitHub でログイン",
        cancelLabel: null
      });
      signIn();
      return;
    }

    cloud.user = { login: me.login, id: me.id };
    const m = loadSync();
    if (m.user !== me.id) {
      // 初めてか、別のアカウント：手元のファイルはすべて「まだ送っていない」として扱う（同じ名前で中身が違えば conflict として残る）
      saveSync({ user: me.id, base: {}, dirty: Object.keys(loadFs()), deleted: {} });
    }
    window.dispatchEvent(new CustomEvent("narfi:files-changed", { detail: { paths: [] } }));
    await syncNow();
    setInterval(() => { if (document.visibilityState === "visible") syncNow(); }, 30000);
    document.addEventListener("visibilitychange", () => { if (document.visibilityState === "visible") syncNow(); });
    window.addEventListener("online", () => syncNow());
  }

  // ---- 画面：右上のアカウントのボタンとメニュー

  const STATE_TEXT = {
    syncing: "同期中…",
    synced: "同期済み",
    pending: "未同期あり",
    offline: "オフライン",
    error: "同期エラー"
  };

  function setCloudState(st) {
    cloud.state = st;
    const b = document.getElementById("btnAccount");
    if (!b) return;
    b.style.display = st === "off" ? "none" : "";
    if (!cloud.user) {
      b.textContent = "Sign in with GitHub";
      b.title = "ログインすると、ファイルがクラウドに保存され、ほかの端末でも開けます";
      b.classList.remove("active");
    } else {
      // GitHub のアイコンと、同期の状態の小さな点
      b.classList.add("account-avatar");
      b.innerHTML = `<img src="https://avatars.githubusercontent.com/u/${encodeURIComponent(cloud.user.id)}?s=64" alt=""><span class="sync-dot ${st}"></span>`;
      b.title = `${cloud.user.login} · ${st === "error" ? `同期できませんでした：${cloud.error}` : STATE_TEXT[st] || ""}`;
    }
  }

  async function saveCurrentFirst() {
    try {
      if (typeof docDirty !== "undefined" && docDirty && typeof saveFile === "function" && currentFilePath) await saveFile({ silent: true });
    } catch (_) {}
  }

  async function signIn() {
    await saveCurrentFirst();
    if (typeof docDirty !== "undefined") docDirty = false; // 移動の確認を出さない（下書きは残る）
    location.href = "/auth/login";
  }

  async function signOut() {
    await saveCurrentFirst();
    await syncNow();
    const m = loadSync();
    const ok = m.dirty.length
      ? await window.uiConfirm("まだクラウドに保存されていない変更があります。ログアウトすると失われます。", "ログアウト", { note: m.dirty.join(", "), danger: true })
      : await window.uiConfirm("ログアウトしますか？", "ログアウト", { note: "ファイルはクラウドに残り、このブラウザからは消えます。" });
    if (!ok) return;
    await cloudFetch("/auth/logout", { method: "POST", body: "{}" });
    localStorage.removeItem(FS_KEY);
    localStorage.removeItem(SYNC_KEY);
    localStorage.removeItem("narfi.lastFile");
    if (typeof docDirty !== "undefined") docDirty = false;
    location.reload();
  }

  async function deleteAccount() {
    const login = cloud.user && cloud.user.login;
    const typed = await window.uiPrompt("アカウントを削除", "", `クラウドのファイルと記録をすべて削除します（GitHub のアカウントはそのままです）。削除するには、ログイン名「${login}」を入力してください。`);
    if (typed === null) return;
    if (typed !== login) { window.uiToast("ログイン名が一致しません"); return; }
    const r = await cloudFetch("/cloud/me", { method: "DELETE" });
    if (!r.ok) { window.uiToast(r.error || "削除できませんでした"); return; }
    localStorage.removeItem(SYNC_KEY);
    location.reload();
  }

  function toggleMenu(anchor) {
    let menu = document.getElementById("accountMenu");
    if (menu) { menu.remove(); return; }
    menu = document.createElement("div");
    menu.id = "accountMenu";
    menu.className = "menu ctx-menu";
    const head = document.createElement("div");
    head.className = "account-head";
    head.textContent = `${cloud.user.login} · ${STATE_TEXT[cloud.state] || ""}`;
    menu.appendChild(head);
    const item = (label, fn, title) => {
      const b = document.createElement("button");
      b.className = "menu-item";
      b.innerHTML = '<span class="mi-label"></span>';
      b.firstChild.textContent = label;
      if (title) b.title = title;
      b.addEventListener("click", () => { menu.remove(); fn(); });
      menu.appendChild(b);
    };
    item("Preferences…", () => window.openPreferences && window.openPreferences());
    item("Sync Now", () => syncNow());
    item("Log Out", signOut);
    item("Delete Account…", deleteAccount);
    const r = anchor.getBoundingClientRect();
    document.body.appendChild(menu);
    menu.style.top = `${r.bottom + 4}px`;
    menu.style.left = `${Math.max(8, r.right - menu.getBoundingClientRect().width)}px`;
    setTimeout(() => document.addEventListener("click", function close(e) {
      if (!menu.contains(e.target)) { menu.remove(); document.removeEventListener("click", close); }
    }), 0);
  }

  window.addEventListener("DOMContentLoaded", () => {
    const right = document.querySelector(".topbar-right");
    if (!right) return;
    const b = document.createElement("button");
    b.id = "btnAccount";
    b.className = "ctrl-btn";
    b.style.display = "none";
    b.addEventListener("click", () => (cloud.user ? toggleMenu(b) : signIn()));
    right.insertBefore(b, document.getElementById("statusPill"));
    ready.then(cloudInit);
  });

  // ---------------------------------------------------------------- /api/… の処理

  function workspace() {
    const fs = loadFs();
    const std = call({ op: "stdlib_list" }).files || [];
    return {
      ok: true,
      web: true,
      root: cloud.user ? `GitHub（${cloud.user.login}）のアカウントに同期` : "このブラウザに保存（GitHub でログインするとクラウドに同期）",
      name: "Files",
      files: Object.keys(fs).sort(),
      dirs: allDirs(fs),
      libs: [{ label: "std", dir: "", files: std }],
      dialogs: true
    };
  }

  // ---- フォルダ（ファイルのパスから分かるものと、空のまま作ったもの）

  const DIRS_KEY = "narfi.dirs.v1";
  function loadDirs() {
    try { return JSON.parse(localStorage.getItem(DIRS_KEY) || "[]"); } catch (_) { return []; }
  }
  function saveDirs(d) {
    localStorage.setItem(DIRS_KEY, JSON.stringify([...new Set(d)].sort()));
  }
  function allDirs(fs) {
    const set = new Set(loadDirs());
    for (const p of Object.keys(fs)) {
      const parts = p.split("/");
      for (let k = 1; k < parts.length; k++) set.add(parts.slice(0, k).join("/"));
    }
    return [...set].sort();
  }
  function validRel(p) {
    return typeof p === "string" && p.length > 0 && p.length <= 200 && !p.startsWith("lib:") &&
      !/[\u0000-\u001f\\]/.test(p) && p.split("/").every((x) => x !== "" && x !== "." && x !== "..");
  }
  function exists(p) {
    const fs = loadFs();
    return p in fs || allDirs(fs).includes(p);
  }

  function createFile(path) {
    if (!validRel(path) || !path.endsWith(".narfi")) return { ok: false, error: "ファイル名は .narfi で終わる名前にしてください" };
    if (exists(path)) return { ok: false, error: `「${path}」はすでにあります` };
    storeFile(path, "");
    return { ok: true, path };
  }

  function makeDir(path) {
    if (!validRel(path)) return { ok: false, error: "フォルダ名が正しくありません" };
    if (exists(path)) return { ok: false, error: `「${path}」はすでにあります` };
    saveDirs([...loadDirs(), path]);
    return { ok: true, path };
  }

  function renamePath(from, to) {
    if (!validRel(from) || !validRel(to)) return { ok: false, error: "名前が正しくありません" };
    if (exists(to)) return { ok: false, error: `「${to}」はすでにあります` };
    const fs = loadFs();
    if (from in fs) {
      if (!to.endsWith(".narfi")) return { ok: false, error: "ファイル名は .narfi で終わる名前にしてください" };
      const src = fs[from];
      removeLocal(from);
      cloudNoteDelete(from);
      storeFile(to, src);
      return { ok: true, path: to };
    }
    if (!allDirs(fs).includes(from)) return { ok: false, error: `「${from}」が見つかりません` };
    if (to.startsWith(from + "/")) return { ok: false, error: "フォルダをその中には移せません" };
    for (const p of Object.keys(fs)) {
      if (!p.startsWith(from + "/")) continue;
      const src = fs[p];
      removeLocal(p);
      cloudNoteDelete(p);
      storeFile(to + p.slice(from.length), src);
    }
    saveDirs(loadDirs().map((d) => (d === from || d.startsWith(from + "/") ? to + d.slice(from.length) : d)));
    return { ok: true, path: to };
  }

  function deletePath(path) {
    if (!validRel(path)) return { ok: false, error: "名前が正しくありません" };
    const fs = loadFs();
    const targets = path in fs ? [path] : Object.keys(fs).filter((p) => p.startsWith(path + "/"));
    if (!(path in fs) && !allDirs(fs).includes(path)) return { ok: false, error: `「${path}」が見つかりません` };
    for (const p of targets) {
      removeLocal(p);
      cloudNoteDelete(p);
    }
    saveDirs(loadDirs().filter((d) => d !== path && !d.startsWith(path + "/")));
    return { ok: true };
  }

  function storeFile(path, src) {
    const fs = loadFs();
    fs[path] = src;
    saveFs(fs);
    call({ op: "put_file", path, src });
    cloudNoteLocalChange(path);
  }

  async function handle(path, query, opts) {
    await ready;
    const body = bodyOf(opts);
    switch (path) {
      case "/api/check":
        return json(call({ op: "check", src: body.src || "", path: body.path && !body.path.startsWith("lib:") ? body.path : "", cursor_line: body.cursor_line || 0, locale: body.locale || "ja" }));
      case "/api/ai_chat": {
        // AI への要求は Pages Functions の中継（functions/cloud/ai.js）へ。キーは保存されない
        const r = await realFetch("/cloud/ai", { method: "POST", credentials: "same-origin", cache: "no-store", headers: { "X-Narfi-Cloud": "1", "Content-Type": "application/json" }, body: JSON.stringify(body) });
        return new Response(await r.text(), { status: r.status, headers: { "Content-Type": "application/json" } });
      }
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
      case "/api/create":
        return json(createFile(body.path));
      case "/api/mkdir":
        return json(makeDir(body.path));
      case "/api/rename":
        return json(renamePath(body.from, body.to));
      case "/api/delete":
        return json(deletePath(body.path));
      case "/api/save-as": {
        let name = await window.uiPrompt("名前を付けて保存", body.name || "note.narfi", "フォルダの中に置くときは week1/note.narfi のように / で区切る");
        if (!name) return json({ ok: false, cancelled: true });
        name = name.trim().replace(/^\/+/, "");
        if (!name.endsWith(".narfi")) name += ".narfi";
        if (!validRel(name)) return json({ ok: false, error: "名前が正しくありません" });
        if (name in loadFs() && !(await window.uiConfirm(`「${name}」はすでにあります。上書きしますか？`, "上書き"))) return json({ ok: false, cancelled: true });
        storeFile(name, body.src || "");
        return json({ ok: true, path: name, src: body.src || "" });
      }
      case "/api/open-file": {
        const files = await pickFiles({ directory: false });
        if (files.length === 0) return json({ ok: false, cancelled: true });
        const f = files[0];
        const src = await f.text();
        if (f.name in loadFs() && !(await window.uiConfirm(`「${f.name}」はすでにあります。読み込んだファイルで上書きしますか？`, "上書き"))) {
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
        if (Object.keys(fs).length === 0) {
          window.uiToast("ダウンロードするファイルがありません");
        } else {
          const stamp = new Date().toISOString().slice(0, 10);
          download(`narfi-${stamp}.zip`, zip(Object.entries(fs)));
        }
        return json({ ok: true });
      }
      case "/api/pdf":
        return json({ ok: false, error: "Print から「PDF として保存」を使ってください" }, 400);
      case "/api/ai":
      case "/api/ai/providers":
        return json({ ok: false, error: "unavailable" });
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

  // Web 版だけ・ローカル版だけの項目は、data-only で出し分ける（web_ui.html の CSS）
  document.documentElement.classList.add("web");
})();
