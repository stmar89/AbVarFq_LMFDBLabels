This repository contains the material for the labelling scheme of abelian varieties over a finite field in an isogeny class with commutative endomorphism algebra $`K`$.
The isomorphism classes of these abelian varieties are functorially represented by fractional ideals in $`K`$.
Hence, we label the corresponding ideal classes.
In the ordinary case, we label also polarizations of the abelian varieties, represented by elements $`K`$.

### Reference
Edgar Costa, Taylor Dupuy, Stefano Marseglia, David Roe, Christelle Vincent<br>
*Labeling abelian varieties over finite fields*, [`arXiv`](https://arxiv.org/abs/2501.17012)

### Installation

1) Get CHIMP, AlgEt and the present package with the following 3 commands:

```
git clone --recurse-submodules -j8 https://github.com/edgarcosta/CHIMP.git
git clone git@github.com:stmar89/AlgEt.git
git clone git@github.com:stmar89/AbVarFq_LMFDBLabels.git
```
-------------------------------------------------------------------------------
2) In Magma, make sure to attach everything by including the following lines (appropriately modified in case you have downloaded the packages in a folder different from your home one):
```
AttachSpec("~/CHIMP/CHIMP.spec");
AttachSpec("~/AlgEt/spec");
AttachSpec("~/AbVarFq_LMFDBLabels/spec");
```
