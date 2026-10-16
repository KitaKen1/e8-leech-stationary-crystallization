"""Scan public theorem names, including nested namespaces and apostrophes.

This supports the project's declaration style. It is a coverage check, not a
Lean parser or proof checker; compiled/exported declaration checks remain required.
"""

import re


def _without_comments(source):
    result = []
    depth = 0
    in_string = False
    escaped = False
    i = 0
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
                continue
            result.append("\n" if char == "\n" else " ")
        elif in_string:
            result.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
            continue
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                result.extend(" " * (len(source) - i))
                break
            result.extend(" " * (end - i))
            i = end
            continue
        elif char == '"':
            in_string = True
            result.append(" ")
        else:
            result.append(char)
        i += 1
    if depth:
        raise ValueError("Unclosed Lean block comment")
    return "".join(result)


def public_theorem_names(source):
    scopes = []
    names = set()
    for line in _without_comments(source).splitlines():
        match = re.match(r"^namespace\s+([\w.']+)\s*$", line)
        if match:
            scopes.append(("namespace", match[1]))
            continue
        match = re.match(r"^(?:noncomputable\s+)?section(?:\s+([\w.']+))?\s*$", line)
        if match:
            scopes.append(("section", match[1]))
            continue
        match = re.match(r"^end(?:\s+([\w.']+))?\s*$", line)
        if match:
            if not scopes:
                raise ValueError("Unmatched Lean end command")
            _, name = scopes.pop()
            if match[1] and match[1] != name:
                raise ValueError(f"Mismatched Lean end: {match[1]} != {name}")
            continue
        match = re.match(r"^(?:@\[[^]]+\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+([\w.']+)", line)
        if match:
            name = match[1]
            if name.startswith("_root_."):
                names.add(name[len("_root_."):])
            else:
                prefix = ".".join(name for kind, name in scopes if kind == "namespace")
                names.add(f"{prefix}.{name}" if prefix else name)
    # Lean permits anonymous sections (including `noncomputable section`) to
    # remain open at the end of a file.
    if any(kind != "section" or name is not None for kind, name in scopes):
        raise ValueError(f"Unclosed Lean scopes: {scopes}")
    return names
