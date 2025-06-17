### A detailed example
After following the instructions for the installatation of all the packages, open magma.
Start by attaching the packages:
```
AttachSpec("~/CHIMP/CHIMP.spec");
AttachSpec("~/AlgEt/spec");
AttachSpec("~/AbVarFq_LMFDBLabels/spec");
```
Consider the isogeny class with LMFDB label [`2.101.abe_pm`](https://abvar.lmfdb.xyz/Variety/Abelian/Fq/2/101/abe_pm). We start by defining the étale algebra `K`, which represents the endomorphism algebra, and will contain all deligne modules representing the isomorphism classes of the abelian varieties.
```
label:="2.101.abe_pm";
g,q,h:=LabelToPoly(label);
K:=EtaleAlgebra(h);
F:=PrimitiveElement(K);
V:=q/F;
ZFV:=Order([F,V]);
```
Now, we compute the weak equivalence classes, their distinguished representatives, and the labels.
This is all done under the hood by the following function, whose output we don't actually need here (it is a string needed to populate the corresponding table in the LMFDB database).
```
_:=FillSchema(ZFV);
```
We loop over all the overorders of `ZFV`, which represent the endomorphisms rings of the abelian varieties, and print the distinguished representatives of all weak equivalence classes with their labels.
```
for S in OverOrders(ZFV) do
    assert assigned S`WKICM_barDistinguishedRepresentatives;
    wkS:=WKICM_barDistinguishedRepresentatives(S);
    for I in wkS do
        WELabel(I);
    end for;
end for;
```
By looking at the labels produced, we see `ZFV` has index 400 in the maximal order of `K` and that are several orders with the same index.
We also see that there are orders which are the multiplicator ring of two weak equivalence classes, showing that `ZFV` is not Gorenstein, but that the biggest Cohen Macaulay type is 2.

We now compute isomorphism classes and their polarizations.
First, we compute a CM-type of `K` satisfying the Shimura-Taniyama formula. This is stored in an attribute.
```
PHI:=pAdicPosCMType(K);
```
We now compute the principal polarizations and print their labels:
```
time all_ppols:=PPolIteration(ZFV);
for pol in all_ppols do
    pol[7];
end for;
```
Now, we compute all polarizations for degrees 4,9 and 25. This can take 4-5 minutes. Then, for each isomorphism class, we print a sequence of pairs <d,n_d> where d is in [4,9,25] and n_d is the number of non-isomorphic polarizations of degree d. If n_d=0 the pair is not printed.
```
time all_pols:=AllNonprincipalPolarizations(ZFV,PHI,[4,9,25]);
for J in Keys(all_pols) do
    J`IsomLabel,[<d,#all_pols[J][d]> : d in Keys(all_pols[J])];
end for;
```

