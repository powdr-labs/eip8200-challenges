#!/usr/bin/env bash
# Re-check the Sha256Fast proof development against this repository's pinned
# toolchain and dependencies.
#
# Usage, from anywhere (the script locates the repository root itself):
#
#   Challenge/Sha256/Candidates/Sha256Fast/verify.sh            # checked tier
#   Challenge/Sha256/Candidates/Sha256Fast/verify.sh --heavy    # + unfinished
#
# ---------------------------------------------------------------------------
# TIERS
#
# The default tier is everything that has been observed to pass on the
# development machine: the 32-bit layer, the block machinery, all sixteen block
# lemmas of the loop body plus loop control, and the axiom-footprint gate over
# all of them.  `Rounds8.lean` dominates it: 15 m 29 s and a 447 MB .olean under
# a 24 GB cap, and an outright failure under a 12 GB one.  Budget ~20 minutes
# and a machine that can spare 24 GB.
#
# Each step deletes its own .olean before elaborating and is skipped if a
# prerequisite failed, so a stale artifact from an earlier attempt can never
# make a later check — including the axiom gate — pass.
#
# `--heavy` additionally attempts `IterSteps.lean` and `SchedIter.lean` and the
# two axiom checks that depend on them.  NEITHER OF THOSE TWO FILES HAS EVER
# ELABORATED TO COMPLETION HERE — both attempts ended in resource exhaustion,
# not in an error.  They are shipped because they are written and sorry-free,
# not because they are checked; the README says so explicitly.  If you have a
# large machine, this tier is exactly the contribution that is wanted, and the
# wall-clock and peak RSS are worth reporting even if it fails.
#
# ---------------------------------------------------------------------------
# RESOURCES — READ THIS BEFORE THE FIRST RUN
#
# Prerequisite: `lake build` must have completed once so the pinned
# EvmSemantics / Challenge.EvmProof .oleans exist.  Note that the repository's
# own build is itself the biggest memory hazard here: a bare `lake build` was
# measured fanning out to five concurrent `lean` workers holding 3.6-8.5 GB
# each, over 36 GB in total and still climbing.  This Lake has no --jobs
# option, but it respects the environment:
#
#   LEAN_NUM_THREADS=2 lake build      # measured: 2 workers, 6.7 GB
#
# MEM_MB caps lean's own allocator so an undersized machine fails with a clean
# "maximum memory exceeded" instead of inviting the kernel OOM killer, which
# will not necessarily choose lean as its victim.  Set it BELOW your free RAM,
# not equal to it.  Run nothing else heavy concurrently.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
SRC="$HERE/proofs"
# Measured: Rounds8.lean fails at MEM_MB=12288 with "(kernel) excessive memory
# consumption" partway through the round lemmas, and completes under 24576.
MEM_MB="${MEM_MB:-24576}"
LOG="${LOG:-$HERE/verify.log}"

HEAVY=false
for arg in "$@"; do
  case "$arg" in
    --heavy) HEAVY=true ;;
    -h|--help) sed -n '2,45p' "$0"; exit 0 ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

cd "$ROOT" || exit 1
[[ -f lakefile.toml ]] || { echo "cannot locate repo root from $HERE" >&2; exit 1; }

# LEAN_PATH must be resolved from the repository root: resolving it elsewhere
# picks up the wrong toolchain or triggers a silent nightly download.
LP="$(lake env printenv LEAN_PATH):$SRC"

: > "$LOG"
fails=0

log() { echo "[$(date +%T)] $*" | tee -a "$LOG"; }

# Every file that failed, so a dependent check is skipped rather than run
# against a stale artifact from an earlier attempt.
failed_files=""

run() {  # run <file.lean> [out.olean] [prerequisite.lean ...]
  local file="$1" out="${2:-}" started elapsed prereq
  shift; [[ $# -gt 0 ]] && shift

  for prereq in "$@"; do
    case " $failed_files " in
      *" $prereq "*)
        log "SKIP $file — its prerequisite $prereq did not pass in this run"
        failed_files="$failed_files $file"
        return
        ;;
    esac
  done

  # A previous run's .olean must not be able to satisfy this one.  Without
  # this, a failed elaboration leaves the old artifact in place and every
  # downstream check — including the axiom gate — passes against stale input.
  [[ -n "$out" ]] && rm -f "$SRC/$out"

  started=$(date +%s)
  log "BEGIN $file (MEM_MB=$MEM_MB)"
  if nice -n 19 env LEAN_PATH="$LP" lake env lean --memory="$MEM_MB" \
      -R "$SRC" ${out:+-o "$SRC/$out"} "$SRC/$file" >> "$LOG" 2>&1; then
    elapsed=$(( $(date +%s) - started ))
    log "OK $file (${elapsed}s)"
  else
    elapsed=$(( $(date +%s) - started ))
    log "FAIL $file (${elapsed}s) — see $LOG; on a small machine expect '(kernel) excessive memory consumption' or 'maximum memory exceeded', which means raise MEM_MB or find a bigger machine, not that the proof is wrong"
    failed_files="$failed_files $file"
    fails=$((fails + 1))
  fi
}

# Order matters: Attr declares the simp attribute Word and Block use, and the
# iteration files elaborate against Rounds8.olean rather than re-elaborating
# the block lemmas.
run Sha256Fast/Attr.lean  Sha256Fast/Attr.olean
run Sha256Fast/Word.lean  Sha256Fast/Word.olean  Sha256Fast/Attr.lean
run Sha256Fast/Block.lean Sha256Fast/Block.olean Sha256Fast/Attr.lean
run Rounds8.lean          Rounds8.olean          Sha256Fast/Block.lean
run AxCheckRounds.lean    ""                     Rounds8.lean

if [[ "$HEAVY" == true ]]; then
  log "--- heavy tier: neither of these files has ever completed on the development machine ---"
  run IterSteps.lean IterSteps.olean Rounds8.lean
  run SchedIter.lean SchedIter.olean Sha256Fast/Block.lean
  run AxCheck.lean      "" IterSteps.lean
  run AxCheckSched.lean "" SchedIter.lean
fi

# The axiom-footprint gate.  Every `#print axioms` line in the log must list
# only the three axioms this challenge admits, and every check that was
# supposed to run must have produced a line — a silently missing check is a
# failure, not a pass.
expected_axiom_lines=14
[[ "$HEAVY" == true ]] && expected_axiom_lines=16

axiom_lines="$(grep -c "depends on axioms\|does not depend on any axioms" "$LOG")"
offenders="$(grep "depends on axioms" "$LOG" \
  | grep -Ev "axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" || true)"

if [[ -n "$offenders" ]]; then
  log "FAIL forbidden axiom in footprint"
  printf '%s\n' "$offenders" | tee -a "$LOG"
  fails=$((fails + 1))
elif [[ "$axiom_lines" -lt "$expected_axiom_lines" ]]; then
  log "FAIL axiom gate incomplete: $axiom_lines of $expected_axiom_lines checks produced output"
  fails=$((fails + 1))
else
  log "axiom gate: $axiom_lines/$expected_axiom_lines results, all [propext, Classical.choice, Quot.sound]"
fi

if [[ $fails -eq 0 ]]; then
  log "DONE all checks passed"
else
  log "DONE $fails check(s) FAILED"
  exit 1
fi
