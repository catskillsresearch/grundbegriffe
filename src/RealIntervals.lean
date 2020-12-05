-- Real closed/open intervals [a,b], (a,b), [a,b), (a,b], (0,1), [0,1], [0,∞).

import data.real.basic
import data.set.intervals.basic
import data.real.ereal

def O01 : set ℝ := set.Ioo 0 1 -- (0,1)
def C01 : set ℝ := set.Icc 0 1 -- [0,1]
def C0oo : set ereal := set.Ici 0 -- [0,∞)
