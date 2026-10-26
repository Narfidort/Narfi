// Web 版の検査器を、画面とは別のスレッド（Web Worker）で動かす（検査中も入力が止まらないように）。
// 画面側（narfi-web.js）から {id, req} を受け取り、narfi.wasm を呼んで {id, res} を返す（id が 0 なら返事はしない）。
// 要求は届いた順に 1 つずつ処理する。検査器の中で止まった（スタックあふれなど）ときは作り直し、
// それまでに登録されたファイルを登録し直してから、その要求を {id, error} として返す。

let wasm = null;
const files = new Map();
const enc = new TextEncoder(), dec = new TextDecoder();

async function instantiate() {
  const resp = await fetch("/narfi.wasm");
  const bytes = await resp.arrayBuffer();
  const { instance } = await WebAssembly.instantiate(bytes, {});
  wasm = instance.exports;
  for (const [path, src] of files) call({ op: "put_file", path, src });
}

function call(req) {
  const b = enc.encode(JSON.stringify(req));
  const p = wasm.narfi_alloc(b.length);
  new Uint8Array(wasm.memory.buffer, p, b.length).set(b);
  const n = wasm.narfi_call(p, b.length);
  wasm.narfi_free(p, b.length);
  return JSON.parse(dec.decode(new Uint8Array(wasm.memory.buffer, wasm.narfi_out_ptr(), n)));
}

let ready = instantiate();
ready.then(() => self.postMessage({ id: -1 }), (err) => self.postMessage({ id: -1, error: String(err) }));
let queue = Promise.resolve();

self.onmessage = (e) => {
  const { id, req } = e.data;
  if (req.op === "put_file") files.set(req.path, req.src);
  if (req.op === "remove_file") files.delete(req.path);
  queue = queue.then(async () => {
    await ready;
    try {
      const res = call(req);
      if (id) self.postMessage({ id, res });
    } catch (err) {
      ready = instantiate();
      await ready;
      if (id) self.postMessage({ id, error: String((err && err.message) || err) });
    }
  });
};
