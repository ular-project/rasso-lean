#!/usr/bin/env python3
"""Run each example with rasso-lean and compare its answer with expected.json.

  python3 tools/check-examples.py [EXAMPLES-DIR]      (default: examples)

Run from the repository's root, after `lake build`. For each EXAMPLES-DIR/*/program.json
(a rassoAST program) it runs `lake exe rasso-lean` and compares with expected.json:

* rows: the last definition's rows, at the expected columns, as a set. The answer may
  have more columns than the expected one;
* objective: the program has exactly one definition whose expression is an enum_sol or
  an enum_msol. Its value is a list that the evaluator orders by the expression's
  `order`, so the first item is the best. Its first key must equal `objective`;
* count: that expression's `of` is a name. That definition's value is a solution set or
  a multi solution set, and its `candidates` must equal `count`.

expected.json says its kind, `"kind": "relation"`, as the Racket implementation's
expected answers do; rasso-lean's examples are relations, so another kind, or none, is
refused. `objective` and `count` may be left out. Exit 1 on any failure.
"""
import json
import os
import subprocess
import sys

KEYS = {"kind", "columns", "rows", "objective", "count"}


def check(folder):
    """The failures for one example, as a list of strings."""
    prog_f, exp_f = os.path.join(folder, "program.json"), os.path.join(folder, "expected.json")
    if not os.path.exists(prog_f):
        return ["expected.json with no program.json"]
    if not os.path.exists(exp_f):
        return ["program.json with no expected.json"]
    program, expected = json.load(open(prog_f)), json.load(open(exp_f))
    if expected.get("kind") != "relation":
        return [f"expected.json must say \"kind\": \"relation\": it has kind {expected.get('kind')!r}"]
    if not {"columns", "rows"} <= set(expected) or set(expected) - KEYS:
        return [f"expected.json must have columns and rows, and only {sorted(KEYS)}: it has {sorted(expected)}"]
    run = subprocess.run(["lake", "exe", "rasso-lean", prog_f], capture_output=True, text=True)
    if run.returncode != 0:
        return [f"rasso-lean failed: {run.stderr.strip()[-500:]}"]
    out = json.loads(run.stdout)
    defs = [i["define"] for i in program["program"] if "define" in i]
    fails = []

    last = out.get(defs[-1]["name"]) if defs else None
    if not isinstance(last, dict) or "rows" not in last:
        fails.append("the last definition has no rows")
    else:
        cols = expected["columns"]
        if not set(cols) <= set(last["columns"]):
            fails.append(f"the answer's columns {last['columns']} lack some of {cols}")
        else:
            at = [last["columns"].index(c) for c in cols]
            got = {json.dumps([r[i] for i in at]) for r in last["rows"]}
            want = {json.dumps(r) for r in expected["rows"]}
            if got != want:
                fails.append(f"rows at {cols}: got {sorted(got)}, expected {sorted(want)}")

    if "objective" in expected or "count" in expected:
        ranked = [d for d in defs if isinstance(d.get("expr"), dict)
                  and set(d["expr"]) & {"enum_sol", "enum_msol"}]
        if len(ranked) != 1:
            return fails + [f"{len(ranked)} definitions are an enum_sol or enum_msol; the rule needs one"]
        d = ranked[0]
        e = d["expr"].get("enum_sol") or d["expr"].get("enum_msol")
        if "objective" in expected:
            items = out.get(d["name"])
            if not isinstance(items, list) or not items or not items[0].get("keys"):
                fails.append(f"{d['name']}: no best item with a key")
            elif items[0]["keys"][0] != expected["objective"]:
                fails.append(f"objective ({d['name']}): got {items[0]['keys'][0]}, expected {expected['objective']}")
        if "count" in expected:
            of = e.get("of") if isinstance(e, dict) else None
            if not isinstance(of, dict) or set(of) != {"name"}:
                fails.append(f"{d['name']}: its `of` is not a name")
            else:
                v = out.get(of["name"], {})
                sets = [v[k] for k in ("solution_set", "multi_solution_set") if isinstance(v, dict) and k in v]
                if not sets:
                    fails.append(f"{of['name']}: not a solution set or a multi solution set")
                elif sets[0]["candidates"] != expected["count"]:
                    fails.append(f"count ({of['name']}): got {sets[0]['candidates']}, expected {expected['count']}")
    return fails


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "examples"
    folders = sorted(os.path.join(root, f) for f in os.listdir(root)
                     if os.path.isdir(os.path.join(root, f)))
    bad = 0
    for f in folders:
        fails = check(f)
        print(("ok    " if not fails else "FAIL  ") + f)
        for x in fails:
            print("      " + x)
        bad += bool(fails)
    print(f"{len(folders)} examples, {bad} failing")
    sys.exit(1 if bad or not folders else 0)


if __name__ == "__main__":
    main()
