/* vim: set syntax=magma :*/

declare attributes AlgEtQOrd: ICM_DistinguishedRepresentatives, RepresentativeMinimalIsogeniesTo;
declare attributes AlgEtQIdl: IsomLabel, // g.q.coeffs-N.i.w.j
                              WErep, Pelt;

is_weak_eq_same_mult_ring:=function(I,J)
// I and J have the same mult ring, and are defined over it
// Similar to the intrinsic IsWeakEquivalent but returns also the colon ideals
    cIJ:=ColonIdeal(I,J);
    cJI:=ColonIdeal(J,I);
    id:=cIJ*cJI;
    test:=One(Algebra(I)) in id;
    return test,cIJ,cJI;
end function;

intrinsic ICM_DistinguishedRepresentatives(ZFV::AlgEtQOrd) -> SeqEnum[AlgEtQIdl], Assoc
{Given the Frobenius order of a squafree isogeny class it returns the distinguished representatives of the isomorphism classes. Each ideal has a label attached to it.}
    if assigned ZFV`ICM_DistinguishedRepresentatives then
        return Explode(ZFV`ICM_DistinguishedRepresentatives);
    end if;
    ans := [];
    icm_lookup := AssociativeArray();
    _ := DistinguishedPicBases(ZFV); // sets bases
    oo:=OverOrders(ZFV);
    isog_label:=IsogenyLabel(DefiningPolynomial(Algebra(ZFV)));

    if exists{S:S in oo | not assigned S`WELabel} then
        oo_sort_keys:=SortKeysOrders(oo);
        ParallelSort(~oo_sort_keys,~oo);
        // orders are now sorted.
        // orders with the same index are grouped together, and already in the right order
        indices_oo:=[ oo_sort_keys[i][1] : i in [1..#oo] ];
        // We construct the labels of the orders
        labels_oo:=[];
        current_index:=indices_oo[1];
        i:=0;
        for iS in [1..#oo] do
            S:=oo[iS];
            N:=indices_oo[iS];
            if N eq current_index then
                i+:=1;
            else
                // we sorted we reset the counter
                i:=1;
                current_index:=N;
            end if;
            S`WELabel:=Sprintf("%o-%o.%o",isog_label,N,i);
        end for;
    end if;
    for iS in [1..#oo] do
        S:=oo[iS];
        basis, _, proj := DistinguishedPicBasis(S);
        icm_lookup[S] := AssociativeArray();
        pic_iter := PicIteration(S, basis : include_pic_elt:=true);
        pic_iter := [<ZFV!!x[1], x[2], x[3]> : x in pic_iter];
        wkS:=WKICM_barDistinguishedRepresentatives(S);
        S`WKICM_bar:=wkS;
        if exists{WE:WE in wkS | not assigned WE`WELabel} then
            wkS_sort_keys:=SortKeysWKICM_bar(S);
            ParallelSort(~wkS_sort_keys,~wkS);
            for j in [1..#wkS] do
                WE:=wkS[j];
                WE`WELabel:=S`WELabel cat Sprintf(".%o",j);
            end for;
        end if;
        for WE in wkS do
            ZFVWE := ZFV!!WE;
            for trip in pic_iter do
                I, ctr, Pelt := Explode(trip);
                WI := ZFVWE * I;
                if assigned WE`WELabel then
                    WI`IsomLabel := Sprintf("%o.%o", WE`WELabel, ctr);
                end if;
                WI`WErep := ZFVWE;
                WI`Pelt := Pelt@@proj;
                icm_lookup[S][<WE, Pelt>] := WI;
                Append(~ans, WI);
            end for;
        end for;
    end for;
    ZFV`ICM_DistinguishedRepresentatives := <ans, icm_lookup>;
    return ans, icm_lookup;
end intrinsic;

intrinsic ICM_Identify(L::AlgEtQIdl, icm_lookup::Assoc) -> AlgEtQIdl, AlgEtQElt, AlgEtQOrd, AlgEtQIdl, GrpAbElt
{Given an ideal L, together with the lookup table output by ICM_DistinguishedRepresentatives, returns the distinguished representative I in the same class of the ICM as L, an element x so that L = x*I, the multiplicator ring S, the distinguished representative W of its weak equivalence class, and the element g in Pic(S) representing the invertible S-ideal (L:W).}
    S := MultiplicatorRing(L);
    PS, pS := PicardGroup(S);
    wkS := WKICM_barDistinguishedRepresentatives(S);
    for i->W in wkS do
        test_wk, cLW, _ := is_weak_eq_same_mult_ring(S!!L,W);
        if test_wk then
            // cLW=(L:W) is invertible, W*cLW = L
            g := cLW@@pS; // in Pic(S)
            I := icm_lookup[S][<W, g>];
            test, x := IsIsomorphic(L, I); // x*I = L
            assert test;
            return I, x, S, W, g;
        end if;
    end for;
end intrinsic;

/*
    SetDebugOnError(true);
    AttachSpec("~/CHIMP/CHIMP.spec");
    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AbVarFq_LMFDBLabels/spec");
    _<x>:=PolynomialRing(Integers());
    f:=x^8+16;
    A:=EtaleAlgebra(f);
    R:=Order(ZFVBasis(A));
    icm_can,icm_lookup:=ICM_DistinguishedRepresentatives(R);

    for L in ICM(R) do 
        _:=ICM_Identify(L,icm_lookup);
    end for;

*/
