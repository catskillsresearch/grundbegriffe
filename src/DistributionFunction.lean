-- Distribution function F_X: ℝ→ [0,1]
-- F_V(E) = P({x \in X: V(x) ≤ e}) be the *distribution function*

-- Clearly F_V(E) is well defined for any metric space (Y,d) provided with a relation a \leq b for all a,b \in Y.

-- All metric spaces can be totally ordered.
-- Not all metric spaces have a total order which is "compatible with the ring structure".  (So: not sensible or useful in that specific sense.)  For example, the complex numbers \mathbb C.
-- 
-- So in the strict sense that all metric spaces can be totally ordered, the distribution function always exists, but it may be "uninteresting".
-- 
-- So to be "obviously useful", it is only necessary to stipulate that the metric space (Y,d) is an "obviously useful" ordered metric space.  Here we have range of possible more or less useful orderings:
-- 
-- Y is a [partially ordered set][2]
-- Y has a partial order compatible with the ring structure
-- Y is a [totally ordered set][3]
-- Y is a [Complete metric space][4]

--  [1]: https://math.stackexchange.com/questions/1429373/why-is-there-no-order-in-metric-spaces
--  [2]: https://en.wikipedia.org/wiki/Partially_ordered_set
--  [3]: https://en.wikipedia.org/wiki/Total_order
--  [4]: https://en.wikipedia.org/wiki/Complete_metric_space
