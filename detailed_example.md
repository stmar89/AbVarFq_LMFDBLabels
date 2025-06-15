### A detailed example
After following the instructions for the installatation of all the packages, open magma.
Start by attaching the packages:
```
AttachSpec("~/CHIMP/CHIMP.spec");
AttachSpec("~/AlgEt/spec");
AttachSpec("~/AbVarFq_LMFDBLabels/spec");
```
Consider the isogeny class with LMFDB label [`3.3.ab_ac_f`](https://abvar.lmfdb.xyz/Variety/Abelian/Fq/3/3/ab_ac_f). We start by defining the étale algebra `K`, which represents the endomorphism algebra, and will contain all deligne modules representing the isomorphism classes of the abelian varieties.
```
label:=3.3.ab_ac_f;
g,q,h:=LabelToPoly(label);
K:=EtaleAlgebra(h);
F:=PrimitiveElement(K);
V:=q/F;
ZFV:=Order([F,V]);
```
Now, we compute the weak equivalence classes, their canonical representatives, and the labels.
This is all done under the hood by the following function, whose output we don't actually need here (it is a string needed to populate the corresponding table in the LMFDB database).
```
_:=FillSchema(ZFV);
```
We loop over all the overorders of ZFV, which represent the endomorphisms rings of the abelian varieties, and print the canonical representatives of all weak equivalence classes with their labels.
```
for S in OverOrders(ZFV) do
    assert assigned S`WKICM_barCanonicalRepresentatives;
    wkS:=WKICM_barCanonicalRepresentatives(S);
    for I in wkS do
        WELabel(I);
    end for;
end for;
```

