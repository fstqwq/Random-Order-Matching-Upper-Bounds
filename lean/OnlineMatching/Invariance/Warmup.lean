import OnlineMatching.Invariance.Memo

/-!
# Cache prewarming

Inserting sound key-value entries into a sound cache preserves soundness, so
any sequence of prewarming insertions followed by the root evaluation returns
the same value as evaluating the root directly.
-/
namespace OnlineMatching.Memo

def publishAll (c : Cache) (entries : List (Key × Value)) : Cache :=
  entries.foldl (fun cache entry => cache.insert entry.1 entry.2) c

theorem publishAll_sound (spec : Key → Value) (entries : List (Key × Value))
    (h : ∀ entry ∈ entries, entry.2 = spec entry.1)
    (c : Cache) (hc : Sound spec c) : Sound spec (publishAll c entries) := by
  induction entries generalizing c with
  | nil => exact hc
  | cons e es ih =>
    apply ih (fun entry he => h entry (by simp [he]))
    exact sound_insert spec c hc e.1 e.2 (h e (by simp))

/-- Prewarming need not contain every state, or even the root. The subsequent
    verified root call handles misses normally. Duplicate writes are allowed. -/
theorem warmup_then_root (spec : Key → Value) (entries : List (Key × Value))
    (h : ∀ entry ∈ entries, entry.2 = spec entry.1)
    (root : Work α) (answer : α) (hr : Correct spec root answer)
    (c : Cache) (hc : Sound spec c) :
    (root.run (publishAll c entries)).1 = answer ∧
    Sound spec (root.run (publishAll c entries)).2 :=
  hr _ (publishAll_sound spec entries h c hc)

end OnlineMatching.Memo
