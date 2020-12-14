import data.finset.basic
open quot

namespace finite_mul_zero_example_fin_3

def X := fin 3
instance : has_mul X := fin.has_mul
instance : has_zero X := fin.has_zero

lemma zero_mul (a : X): 0 * a = 0 := 
begin
  sorry
end

lemma mul_zero (a : X): a * 0 = 0 := 
begin
  sorry
end

instance : mul_zero_class X := {
 mul := (*),
 zero := 0,
 zero_mul := zero_mul,
 mul_zero := mul_zero }

end finite_mul_zero_example_fin_3
