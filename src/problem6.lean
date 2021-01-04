import algebra.ring.basic
import tactic

namespace ex_6a

structure integralDomain 
      (α: Type) (R: set α) [has_mem α (set α)]  
      (zed : R) (une : R) (plus : R → R → R) (mul: R → R → R) : Prop :=
(zeroness: ∀ (a : R),  (plus a zed) = a)
(oneness: ∀ (a : R),  (mul a une) = a)
(cancellation: ∀ (a b c : R),  (c ≠ zed → mul c a = mul c b → a = b))
(uniqueness: ∀ (a a' b b' : R),  (a=a' → b=b' → mul a b = mul a' b'))
(comm_add: ∀ (a b : R),  plus a b = plus b a)
(comm_mul: ∀ (a b : R),  mul a b = mul b a)
(assoc_add: ∀ (a b c : R),  plus a (plus b c) = plus (plus a b) c)
(assoc_mul: ∀ (a b c : R),  mul a (mul b c) = mul (mul a b) c)
(dist: ∀ (a b c : R),  mul a (plus b c) = plus (mul a b) (mul a c))
(add_inv: ∀ (a : R),  ∃ (x : R), plus a x = zed)

theorem ex6a : 
  ¬ (∃ (zed : {x : ℤ | even x}), -- has a zero
     ∃ (une : {x : ℤ | even x}),  -- has a one
     ∃ (plus : {x : ℤ | even x} → {x : ℤ | even x} → {x : ℤ | even x}), -- has add
     ∃ (mul : {x : ℤ | even x} → {x : ℤ | even x} → {x : ℤ | even x}), -- has mul
        ((∀ (x : {x : ℤ | even x}), ∃ (y : {x : ℤ | even x}), x = plus y y) ∧ 
         (@integralDomain ℤ {x : ℤ | even x} _ zed une plus mul))):=
begin
  intro h1,
  cases h1 with zed h2,
  cases h2 with une h3,
  cases h3 with plus h4,
  cases h4 with mul h5,
  have h6 := h5.left,
  have h7 := h5.right,
  have h8 := h7.oneness une,
  have h9 := h7.dist une une une,
  have h10 := h6 une,
  cases h10 with y hy,
  sorry
end

end ex_6a
