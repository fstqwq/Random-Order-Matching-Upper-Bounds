import OnlineMatching.Basic

/-!
# Scaling identities for the integer recurrence

Algebraic lemmas relating the rational Bellman recurrence and its
division-free integer form.
-/
namespace OnlineMatching.IntegerScaling

theorem scale_max (z a b : Rat) (hz : 0 ≤ z) :
    max (z*a) (z*b) = z * max a b := by
  by_cases h : a ≤ b
  · have hm := Rat.mul_le_mul_of_nonneg_left h hz
    simp only [Rat.max_def, h, hm, ite_true]
  · have hba : b ≤ a := by grind
    have hm := Rat.mul_le_mul_of_nonneg_left hba hz
    rw [Rat.max_def, Rat.max_def]
    split <;> grind

theorem scaled_accept_reject (z reject accept : Rat) (hz : 0 ≤ z) :
    max (z*reject) (z+z*accept) = z * max reject (1+accept) := by
  have he : z + z*accept = z*(1+accept) := by
    rw [Rat.mul_add, Rat.mul_one]
  rw [he]
  exact scale_max z reject (1+accept) hz

theorem cancel_parent_scale (parent child multiplicity value : Rat)
    (hp : parent ≠ 0) :
    parent * ((multiplicity*child/parent)*value) =
      multiplicity*(child*value) := by
  have h : (multiplicity*child/parent)*parent = multiplicity*child :=
    Rat.div_mul_cancel hp
  grind

theorem final_normalization (scaled scale value matching : Rat)
    (hs : scale ≠ 0) (h : scaled = scale*value) :
    scaled/(scale*matching) = value/matching := by
  subst scaled
  simp only [Rat.div_def, Rat.inv_mul_rev]
  have hh := Rat.mul_inv_cancel scale hs
  grind

end OnlineMatching.IntegerScaling
