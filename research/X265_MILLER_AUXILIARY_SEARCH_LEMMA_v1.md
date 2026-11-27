# X265 production pseudocode addendum — Miller auxiliary-point search

Replace any unspecified or fixed-cap auxiliary-point search in the noncyclic Weil certificate with the following proof-level routine.

Input: \(E/\mathbb F_p\), \(n>1\), \(P,Q\in E[n](\mathbb F_p)\), with \(n\mid p-1\).

1. If \(P=O\), \(Q=O\), or \(P=Q\), return \(1\) (the exact-order check will reject it as a primitive value when \(n>1\)).
2. Repeat:
   - sample \(R\) uniformly from \(E(\mathbb F_p)\);
   - reject \(R\) if \(R\in\{O,P,-Q,P-Q\}\);
   - compute the four Miller evaluations \(f_{n,P}(Q+R)\), \(f_{n,P}(R)\), \(f_{n,Q}(-R)\), \(f_{n,Q}(P-R)\);
   - reject this \(R\) if any intermediate line factor is zero or has a pole;
   - form the shifted-divisor ratio (12) in X268 and check \(\eta^n=1\);
   - return \(\eta\).
3. The independent verifier receives \(R\), recomputes all four Miller values and the ratio, and checks exact order \(n\) by testing \(\eta^n=1\) and \(\eta^{n/\ell}\ne1\) for every distinct prime \(\ell\mid n\).

For each Miller line quotient, the numerator line has at most three intersections with \(E\), and the vertical denominator at most two. Thus each factor has at most five zero/pole evaluation points. Four Miller runs have at most \(8\lfloor\log_2n\rfloor\) factors. The four translated arguments are bijections of the auxiliary point. Hence at most \(40\lfloor\log_2n\rfloor+4\) auxiliary points are rejected.

For \(N\ge1024\) and \(n\le N\), this is at most \(N/2\), so a uniform auxiliary point is good with probability at least \(1/2\), and the expected number of trials is at most two. Uniform point sampling has constant expected rejection overhead by Hasse. The full Weil computation and auxiliary search therefore cost \(\operatorname{polylog}N\) expected bit operations.

The existing Python reference routine's fixed 600-iteration cap is not the proof. Either implement the expected-time loop above, or keep a finite cap and include its explicit failure probability in the outer attempt analysis.