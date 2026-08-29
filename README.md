# Lambda calculus with explicit alpha-steps, in Agda

In this repo, I using Agda to develop some of the theory of lambda calculus using a version of Church's original system, where renaming bound variables is done with explicit steps.  (The name alpha to describe those steps arose later.)

The standard approach to formalizing lambda calculus is to use de Bruijn indices, so that there are no bound variables at all.  While there are some benefits of this approach, it is not clear how one would formalize theorems that are explicitly about alpha-equivalence.  An example of such a theorem is that a term with variables sufficiently distinct can be completely developed without any alpha-steps.  Complete development means that all the redexes appearing in the term, and their residuals, are reduced, but no created redexes are reduced.

My development now includes a formal proof this theorem, as `⇒αtk` in [Parallel.agda](agda-code/Parallel.agda#L103).