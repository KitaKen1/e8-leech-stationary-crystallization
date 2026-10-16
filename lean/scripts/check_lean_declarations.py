"""Regression checks for the declaration coverage scanner."""

from lean_declarations import public_theorem_names

source = '''
/- namespace Wrong
/- theorem alsoWrong : True := by trivial -/
theorem wrong : True := by trivial
-/
noncomputable section
namespace E8Leech.Taylor
section Bounds
@[simp] theorem endpoint' : True := by trivial
private theorem hidden : True := by trivial
namespace TM
@[simp] @[local simp] theorem lower_le : True := by trivial
end TM
end Bounds
-- theorem commented : True := by trivial
def prose := "namespace Wrong\\\"\n theorem notACertificate : True := by trivial"
lemma _root_.standalone : True := by trivial
end E8Leech.Taylor
end
'''
assert public_theorem_names(source) == {
    "E8Leech.Taylor.endpoint'", "E8Leech.Taylor.TM.lower_le", "standalone",
}
assert public_theorem_names("noncomputable section\nnamespace A\ntheorem t : True := by trivial\nend A") == {"A.t"}
for malformed in ["end", "namespace A\nend B", "/- unfinished", "namespace A"]:
    try:
        public_theorem_names(malformed)
    except ValueError:
        pass
    else:
        raise AssertionError(f"Malformed scope was accepted: {malformed}")
print("Declaration coverage scanner regression checks passed")
