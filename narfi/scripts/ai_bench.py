#!/usr/bin/env python3
"""AI に Narfi の練習を解かせて、narfi check で採点する（モデル選びのため）。

    python3 scripts/ai_bench.py [モデル ...]

接続先とキーは .dev.vars の AI_BASE_URL・AI_API_KEY（OpenAI と同じ形式の chat/completions）。
各問：説明（docs/language/syntax.md）と問題を渡し、通らなければエラーを返して最大 RETRIES 回直させる。
費用は models.dev の価格表から計算する（キャッシュの割引は数えない）。
"""
import json, os, re, subprocess, sys, tempfile, threading, time, urllib.request, uuid

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RETRIES = 3
# gpt-6-luna・claude-haiku-5-5 は chat/completions では呼べない（ModelProtocolUnsupported）
DEFAULT_MODELS = ["mimo-v2.6-flash", "deepseek-v4.1-flash", "glm-5.3-flash", "qwen3.8-flash",
                  "minimax-m3", "mimo-v2.6-pro", "deepseek-v4-pro", "glm-5.3"]


def env():
    vals = {}
    for line in open(os.path.join(ROOT, ".dev.vars")):
        if "=" in line and not line.lstrip().startswith("#"):
            k, v = line.strip().split("=", 1)
            vals[k] = v
    return vals["AI_BASE_URL"].rstrip("/"), vals["AI_API_KEY"]


def exercises():
    s = open(os.path.join(ROOT, "src/tutorial.js")).read()
    return [json.loads('"' + m + '"') for m in re.findall(r'"exercise": "((?:[^"\\]|\\.)*)"', s)]


def prices():
    try:
        req = urllib.request.Request("https://models.dev/api.json", headers={"User-Agent": "narfi-ai-bench/0.1"})
        d = json.load(urllib.request.urlopen(req, timeout=20))
        return {k: v.get("cost", {}) for k, v in d.get("opencode-go", {}).get("models", {}).items()}
    except Exception:
        return {}


SYSTEM = """You write proofs in Narfi, a natural-deduction proof language. The full syntax reference follows.
Replace `sorry` with a proof. Keep the theorem statement and everything else unchanged.
Answer with the whole file in one ```narfi code block and nothing else. Use ASCII spellings
(forall, exists, ->, and, or, not, |-, <=, >=, Real, Nat, Prop) as in the exercise.

""" + open(os.path.join(ROOT, "..", "docs/language/syntax.md")).read()


def chat(base, key, model, session, messages):
    body = json.dumps({"model": model, "messages": messages, "max_tokens": 8000}).encode()
    req = urllib.request.Request(base + "/chat/completions", data=body, headers={
        "Authorization": "Bearer " + key, "Content-Type": "application/json",
        "User-Agent": "narfi-ai-bench/0.1", "x-opencode-session": session})
    d = json.load(urllib.request.urlopen(req, timeout=300))
    if "choices" not in d:
        raise RuntimeError(str(d)[:200])
    return d["choices"][0]["message"].get("content") or "", d.get("usage", {})


def check(src):
    with tempfile.NamedTemporaryFile("w", suffix=".narfi", delete=False) as f:
        f.write(src)
    r = subprocess.run([os.path.join(ROOT, "target/debug/narfi"), "check", f.name], capture_output=True, text=True, timeout=60)
    os.unlink(f.name)
    out = (r.stdout + r.stderr).replace(f.name, "answer.narfi")
    return r.returncode == 0 and "sorry" not in src, out


def code_of(text):
    m = re.findall(r"```(?:narfi)?\n(.*?)```", text, re.S)
    return m[-1] if m else text


def run_model(base, key, model, exs, cost, results):
    rows = []
    for i, ex in enumerate(exs):
        msgs = [{"role": "system", "content": SYSTEM}, {"role": "user", "content": ex}]
        session = f"narfi-bench-{uuid.uuid4()}"
        t0, tin, tout, ok, tries, err = time.time(), 0, 0, False, 0, ""
        for tries in range(1, RETRIES + 2):
            try:
                text, u = chat(base, key, model, session, msgs)
            except Exception as e:
                err = str(e)[:120]
                break
            tin += u.get("prompt_tokens", 0)
            tout += u.get("completion_tokens", 0)
            src = code_of(text)
            ok, out = check(src)
            if ok:
                break
            msgs += [{"role": "assistant", "content": text},
                     {"role": "user", "content": "narfi check failed:\n" + out[-2000:] + "\nFix it and answer with the whole file again."}]
        usd = (tin * cost.get("input", 0) + tout * cost.get("output", 0)) / 1e6
        rows.append({"ex": i + 1, "ok": ok, "tries": tries, "sec": time.time() - t0, "in": tin, "out": tout, "usd": usd, "err": err})
        print(f"  {model:22} 練習{i+1:2} {'✓' if ok else '✗'} {tries}回 {time.time()-t0:5.0f}s ${usd:.4f} {err}", flush=True)
    results[model] = rows


def main():
    base, key = env()
    models = sys.argv[1:] or DEFAULT_MODELS
    exs, cost = exercises(), prices()
    results, threads = {}, []
    for m in models:
        t = threading.Thread(target=run_model, args=(base, key, m, exs, cost.get(m, {}), results))
        t.start()
        threads.append(t)
    for t in threads:
        t.join()
    print("\n| モデル | 正解 | 1 回目で正解 | 平均の時間 | 費用（10 問） | 正解 1 問あたり |")
    print("|---|---|---|---|---|---|")
    for m in models:
        r = results.get(m, [])
        n = sum(x["ok"] for x in r)
        first = sum(x["ok"] and x["tries"] == 1 for x in r)
        usd = sum(x["usd"] for x in r)
        sec = sum(x["sec"] for x in r) / max(len(r), 1)
        per = f"${usd / n:.4f}" if n else "-"
        print(f"| {m} | {n}/{len(r)} | {first} | {sec:.0f}s | ${usd:.4f} | {per} |")
    json.dump(results, open("/tmp/narfi-ai-bench.json", "w"), indent=1)


if __name__ == "__main__":
    main()
