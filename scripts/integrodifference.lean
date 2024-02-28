import Mathlib.Analysis.Convolution
structure IDE where
  T: Type
  X: MeasurableSpace T
  g: Real -> Real
  k: T -> T -> Real
  ok_g: Measurable g
  ok_k: Measurable k
def ide_step (ide: IDE) (u: Real -> Real) : Real -> Real := convolution u u sorry
