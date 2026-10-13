import re
import sys

BASE = {"propext", "Classical.choice", "Quot.sound"}
PATTERNS = [
    re.compile(r"(Chess\.)?All63\.u\d{4}_[0-9a-f]{16}"),
    re.compile(r"(Chess\.)?C364\.r\d{4}_[0-9a-f]{16}"),
    re.compile(r"(Chess\.)?All63\.ok63\._native\.native_decide\.ax_\d+(_\d+)*"),
]


def allowed(a):
    return a in BASE or any(p.fullmatch(a) for p in PATTERNS)


def main():
    strict = "--final" in sys.argv
    text = sys.stdin.read()
    if "error" in text.lower() and "depends on axioms" not in text:
        print(text)
        sys.exit(1)
    blocks = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.S)
    if not blocks:
        print(text)
        print("GATE: no axiom report found")
        sys.exit(1)
    fail = False
    for name, lst in blocks:
        axs = [a.strip() for a in lst.replace("\n", " ").split(",") if a.strip()]
        bad = [a for a in axs if a != "sorryAx" and not allowed(a)]
        u = sum(1 for a in axs if PATTERNS[0].fullmatch(a))
        r = sum(1 for a in axs if PATTERNS[1].fullmatch(a))
        nd = sum(1 for a in axs if "native_decide" in a)
        has_sorry = "sorryAx" in axs
        print(f"{name}: {len(axs)} axioms ({u} 63-case, {r} 364-record, {nd} native_decide), "
              f"sorryAx={'yes' if has_sorry else 'no'}, outside trust base={bad[:10]}")
        if bad or (strict and has_sorry):
            fail = True
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
