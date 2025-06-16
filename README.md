### Introduction
This repository contains the Magma code implementing the labelling scheme for abelian varieties over a finite field in an isogeny class with commutative endomorphism algebra $`K`$ described in the reference below.<br>
The isomorphism classes of these abelian varieties are functorially represented by fractional ideals in $`K`$.
Hence, we label the corresponding ideal classes.<br>
In the ordinary case, we label also polarizations of the abelian varieties, represented by elements of $`K`$.

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

### A detailed example
In the [`example file`](https://github.com/stmar89/AbVarFq_LMFDBLabels/blob/main/detailed_example.md), we exhibit how to use the various intrinsics to compute isomorphism classes, polarizations and labels for a specific isogeny class.

### Further info
The folder `computation/` contains scripts for the computation and labeling of the isomorphism classes with polarizations used to populate (some entries of) the LMFDB tables `av_fq_isog`, `av_fq_weak_equivalences` and `av_fq_pol`.<br>
See `computation/Makefile` for more details.
