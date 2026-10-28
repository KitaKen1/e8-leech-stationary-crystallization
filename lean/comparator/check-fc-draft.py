#!/usr/bin/env python3
"""Check the actual FC overlay and its correspondence to canonical proof types."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys, time
PRIMARY = ['e8_quantitative_crystallization', 'leech_quantitative_crystallization']
TESTS = ['zero_mem_e8Set', 'zero_mem_leechSet']
DEFINITIONS = ['e8Set', 'golayBlock', 'leechSet', 'QuantitativeCrystallization']
LINTERS = ['style.copyright.formalConjectures', 'style.namespace', 'style.stubs',
           'style.openClassical', 'style.ams_attribute', 'style.category_attribute',
           'style.conditional_formal_proof', 'style.moduleDocstring',
           'style.latex_docstring', 'style.imports', 'privateModule']

def clean(s):
    return re.sub(r'\s+', ' ', s).strip()

def target(s, name):
    match = re.search(r'^theorem ' + re.escape(name) + r' [\s\S]*? := by\n  sorry', s, re.M)
    if match is None:
        raise RuntimeError('Missing FC primary statement: ' + name)
    return match.group()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

MODEL_CHECKS = r"""
namespace FCStyleModel
open scoped ENNReal
example (d : ℕ) : configurationMeasurableSpace (X := Ambient d) =
    (inferInstance : MeasurableSpace (Configuration (Ambient d))) := by rfl
example {d : ℕ} (a : Ambient d) : translate a = E8Leech.translate a := by rfl
example {d : ℕ} (μ : MeasureTheory.Measure (Configuration (Ambient d))) :
    IsStationary μ = E8Leech.IsStationary μ := by rfl
example {d : ℕ} (μ : MeasureTheory.Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) :
    HasIntensity μ ρ = E8Leech.HasIntensity μ ρ := by rfl
example : e8Set = E8Leech.e8Set := by rfl
example : golayBlock = E8Leech.golayBlock := by rfl
lemma leechSet_eq : leechSet = E8Leech.leechSet := by
  apply congrArg (fun S : Set (Fin 24 → ℤ) => E8Leech.leechCoordinates '' S)
  ext z
  simp only [E8Leech.leechNumerators, Set.mem_ofPred_eq,
    E8Leech.golayCode, LinearMap.mem_range]
  rfl
lemma rieszEnergy_eq {d : ℕ} (s : ℝ) (μ : MeasureTheory.Measure (Configuration (Ambient d))) :
    rieszEnergy s μ = E8Leech.rieszEnergy s μ := by
  unfold rieszEnergy E8Leech.rieszEnergy E8Leech.orderedWindowEnergy
    E8Leech.rieszPotential E8Leech.unitWindow
  apply MeasureTheory.lintegral_congr
  intro c
  apply tsum_congr
  intro x
  by_cases hx : (x : Ambient d) ∈ {u | ∀ i, u i ∈ Set.Ico (0 : ℝ) 1}
  · simp only [if_pos hx]
    apply tsum_congr
    intro y
    split_ifs <;> rfl
  · simp only [if_neg hx]
example {d : ℕ} (Λ : Set (Ambient d)) (s : ℝ) :
    latticeRieszEnergy Λ s = E8Leech.latticeRieszEnergy Λ s := by rfl
example {d : ℕ} (Λ : Set (Ambient d)) (c : Configuration (Ambient d))
    (R error loss : ℝ) :
    LocalCrystal Λ c R error loss = E8Leech.LocalCrystal Λ c R error loss := by rfl
end FCStyleModel
"""

def generate_bridge(support, draft, challenge):
    core = support[support.index('noncomputable section'):]
    core = core.replace('namespace PointProcess', 'namespace FCStyleModel')
    core = core.replace('end PointProcess', 'end FCStyleModel')
    core = re.sub(r'structure Configuration [\s\S]*?(?=\ninstance)',
        'abbrev Configuration (X : Type*) [TopologicalSpace X] := E8Leech.Configuration X\n',
        core, count=1)
    core = core.replace('instance {X : Type*}', 'abbrev configurationMeasurableSpace {X : Type*}', 1)
    body = draft.split('namespace E8LeechFC\n', 1)[1]
    definitions = body[:body.index('/-- Quantitative stationary crystallization for $E_8$')]
    definitions = definitions.replace('open PointProcess', 'open FCStyleModel')
    chunks = []
    for tag in ['e8', 'leech']:
        name = tag + '_quantitative_crystallization'
        statement = target(draft, name).rsplit('  sorry', 1)[0]
        goal = target(challenge, name).split(' :\n', 1)[1].rsplit(' := by', 1)[0]
        for term in ['Configuration', 'Ambient', 'IsStationary', 'HasIntensity', 'rieszEnergy',
                     'latticeRieszEnergy', 'e8Set', 'leechSet', 'LocalCrystal', 'observationRadius']:
            goal = re.sub(r'\b' + term + r'\b', 'E8Leech.' + term, goal)
        proof = ('  unfold FCStyleModel.QuantitativeCrystallization\n'
                 '  simp only [FCStyleModel.rieszEnergy_eq]\n')
        if tag == 'leech':
            proof += '  rw [FCStyleModel.leechSet_eq]\n'
        proof += ('  change ' + goal.strip() + '\n  exact E8Leech.' + tag +
                  '_crystallization_of_energy_le_general hs hγ hγlt\n')
        chunks.append(statement + proof)
    return ('import E8Leech\n\n' + core + '\nnamespace FCStyleModel\n' + definitions +
            '\nend FCStyleModel\n' + MODEL_CHECKS +
            '\nnamespace FCStyleProof\nopen FCStyleModel Set MeasureTheory\nopen scoped ENNReal\n' +
            '\n'.join(chunks) + '\nend FCStyleProof\n' +
            ''.join('#print axioms FCStyleProof.' + n + '\n' for n in PRIMARY))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--compile', action='store_true')
    parser.add_argument('--receipt-dir', type=Path)
    parser.add_argument('--fc-root', type=Path)
    parser.add_argument('--packages', type=Path)
    parser.add_argument('--offline', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    draft_path = root / 'FClikelean/E8Leech.lean'
    support_path = root / 'FClikelean/FormalConjecturesForMathlib/Probability/SimplePointProcess.lean'
    draft, support = draft_path.read_text(), support_path.read_text()
    challenge_path = root / 'lean/Challenge.lean'
    challenge = challenge_path.read_text()
    sys.path.insert(0, str(root / 'lean/scripts'))
    from lean_declarations import _without_comments
    mathematics, generic = _without_comments(draft), _without_comments(support)
    assert re.findall(r'^(?:public )?import (\S+)', mathematics, re.M) == ['FormalConjecturesUtil']
    assert draft.startswith('module\n') and '\npublic import FormalConjecturesUtil\n' in draft
    assert '@[expose] public section' in mathematics and '*Reference:*' in draft
    assert re.findall(r'^def (\w+)', mathematics, re.M) == DEFINITIONS
    assert re.findall(r'^theorem (\w+)', mathematics, re.M) == PRIMARY + TESTS
    assert mathematics.count('@[category research solved, AMS 52 60]') == 2
    assert mathematics.count('@[category test, AMS 52]') == 2
    assert len(re.findall(r'\bsorry\b', mathematics)) == 2
    assert not re.search(r'\b(sorry|admit|axiom|opaque|constant|native_decide)\b', generic)
    assert not re.search(r'\b(admit|axiom|opaque|constant|native_decide)\b', mathematics)
    assert all(m.startswith('Mathlib.') for m in re.findall(r'^public import (\S+)', generic, re.M))
    reference_path = root / 'lean/FCDefinitions/Configuration.lean'
    def structure(s):
        return re.search(r'^structure Configuration [\s\S]*?^  finite_on_compacts[^\n]*', s, re.M).group()
    assert clean(structure(support)) == clean(structure(reference_path.read_text())), 'Configuration fields changed'
    for name in PRIMARY:
        assert clean(target(draft, name).split(' :\n', 1)[0]) == clean(target(challenge, name).split(' :\n', 1)[0]), name
    result = dict(success=True, static_checks_passed=True, problem_definition_count=4,
        generic_definition_count=len(re.findall(r'^def (\w+)', generic, re.M)),
        primary_theorems=PRIMARY, proved_boundary_tests=TESTS,
        source_sha256=sha(draft_path), support_sha256=sha(support_path),
        canonical_challenge_sha256=sha(challenge_path), configuration_reference_sha256=sha(reference_path),
        checker_sha256=sha(Path(__file__)), semantic_correspondence_checked=False,
        original_manuscript_review_complete=False, actual_fc_linter_checked=False)
    if args.compile:
        start = time.monotonic()
        receipt = args.receipt_dir.resolve() if args.receipt_dir else root / 'verification'
        receipt.mkdir(parents=True, exist_ok=True)
        fc_root = (args.fc_root or root / 'lean/.lake/fc-upstream').resolve()
        spec = importlib.util.spec_from_file_location('prepare_fc', Path(__file__).with_name('prepare-fc.py'))
        prepare_fc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(prepare_fc)
        fc_env, upstream = prepare_fc.prepare(root, fc_root,
            (args.packages or root / 'lean/.lake/packages').resolve(), offline=args.offline)
        problem = fc_root / 'FormalConjectures/Paper/E8Leech.lean'
        problem.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(draft_path, problem)
        options = ['-j1', '-DElab.async=false', '-Dpp.unicode.fun=true',
                   '-DautoImplicit=false', '-DrelaxedAutoImplicit=false']
        def run(source, log, env, cwd, extra=()):
            process = subprocess.run(['lean', *options, *extra, str(source)], cwd=cwd,
                env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=900)
            (receipt / log).write_text(process.stdout)
            if process.returncode:
                raise RuntimeError(process.stdout[-16000:])
            return process.stdout
        lint_options = ['-Dwarn.sorry=false'] + ['-Dweak.linter.' + n +
            ('=false' if n == 'style.copyright.formalConjectures' else '=true') for n in LINTERS]
        linted = run(problem, 'local-FClikelean.log', fc_env, fc_root, lint_options)
        assert 'warning:' not in linted, linted
        # A negative control confirms that the genuine upstream linters are
        # active at the intended FormalConjectures module path.
        control = problem.with_name('E8LeechLinterControl.lean')
        control_text = draft[:draft.index('noncomputable section')].replace(
            'public import FormalConjecturesUtil',
            'public import FormalConjecturesUtil\npublic import Mathlib.Data.Nat.Basic')
        control_text += ('namespace FCStyleControl\n/-- Linter activation test. -/\n'
                         '@[category test]\ntheorem control : True := by trivial\n'
                         'end FCStyleControl\n')
        control.write_text(control_text)
        try:
            warnings = run(control, 'local-FClikelean-linter-control.log', fc_env, fc_root, lint_options)
            assert 'Missing AMS attribute.' in warnings, warnings
            assert "Direct imports from 'Mathlib'" in warnings, warnings
            assert warnings.count('warning:') == 2, warnings
        finally:
            control.unlink(missing_ok=True)
        (receipt / 'local-FClikelean-linter-control.json').write_text(json.dumps(dict(
            success=True, expected_warning_count=2, observed_warning_count=2,
            controls=['missing AMS tag', 'forbidden direct Mathlib import'],
            copyright_header_linter_enabled=False,
            upstream_commit=upstream['upstream_commit']), indent=2) + '\n')
        (receipt / 'local-FClikelean.json').write_text(json.dumps(dict(success=True,
            exit_code=0, source_sha256=sha(draft_path), support_sha256=sha(support_path),
            actual_fc_linter_checked=True, linter_options=lint_options, upstream=upstream,
            actual_fc_linter_negative_control_passed=True,
            copyright_header_linter_enabled=False,
            expected_statement_sorry_count=2, proved_boundary_tests=TESTS,
            imports_development_proof=False), indent=2) + '\n')
        out = root / 'lean/.lake/fc-style-check'
        out.mkdir(parents=True, exist_ok=True)
        bridge = out / 'FCStyleProof.lean'
        bridge.write_text(generate_bridge(support, draft, challenge))
        env = os.environ.copy()
        env['LEAN_NUM_THREADS'] = '1'
        checked = run(bridge, 'local-FClikelean-correspondence.log', env, root / 'lean')
        assert 'warning:' not in checked, checked
        observed = {n: {x.strip() for x in values.split(',') if x.strip()}
                    for n, values in re.findall(r"'(FCStyleProof\.[^']+)' depends on axioms:\s*\[([^\]]*)\]", checked, re.S)}
        assert set(observed) == {'FCStyleProof.' + n for n in PRIMARY}, observed
        assert all(axioms <= {'propext', 'Classical.choice', 'Quot.sound'} for axioms in observed.values()), observed
        result.update(semantic_correspondence_checked=True, actual_fc_linter_checked=True,
            copyright_header_linter_enabled=False,
            method='Identical Configuration fields, kernel-checked counting sigma algebra and compact definition equalities, and change to exact canonical primary conclusions',
            upstream=upstream, proof_bridge_sha256=sha(bridge), elapsed_seconds=time.monotonic() - start,
            axioms={n: sorted(ax) for n, ax in observed.items()},
            draft_proof_holes_used=False, development_proof_objects_reused=True)
        (receipt / 'fc-style-correspondence.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
