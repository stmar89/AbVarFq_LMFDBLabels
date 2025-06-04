/* vim: set syntax=magma :*/

declare attributes AlgEtQOrd: ICM_CanonicalRepresentatives, RepresentativeMinimalIsogeniesTo;
declare attributes AlgEtQIdl: IsomLabel, WErep, Pelt;

is_weak_eq_same_mult_ring:=function(I,J)
// I and J have the same mult ring, and are defined over it
// Similar to the intrinsic IsWeakEquivalent but returns also the colon ideals
    cIJ:=ColonIdeal(I,J);
    cJI:=ColonIdeal(J,I);
    id:=cIJ*cJI;
    test:=One(Algebra(I)) in id;
    return test,cIJ,cJI;
end function;

intrinsic ICM_CanonicalRepresentatives(ZFV::AlgEtQOrd) -> SeqEnum[AlgEtQIdl], Assoc
{Given the Frobenius order of a squafree isogeny class it returns the canonical representatives of the isomorphism classes. Each ideal has a label attached to it.}
    if assigned ZFV`ICM_CanonicalRepresentatives then
        return Explode(ZFV`ICM_CanonicalRepresentatives);
    end if;
    ans := [];
    icm_lookup := AssociativeArray();
    _ := CanonicalPicBases(ZFV); // sets bases
    for S in OverOrders(ZFV) do
        basis, _, proj := CanonicalPicBasis(S);
        icm_lookup[S] := AssociativeArray();
        pic_iter := PicIteration(S, basis : include_pic_elt:=true);
        pic_iter := [<ZFV!!x[1], x[2], x[3]> : x in pic_iter];
        for WE in WKICM_barCanonicalRepresentatives(S) do
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
    ZFV`ICM_CanonicalRepresentatives := <ans, icm_lookup>;
    return ans, icm_lookup;
end intrinsic;

intrinsic ICM_Identify(L::AlgEtQIdl, icm_lookup::Assoc) -> AlgEtQIdl, AlgEtQElt, AlgEtQOrd, AlgEtQIdl, GrpAbElt
{Given an ideal L, together with the lookup table output by ICM_CanonicalRepresentatives, returns the canonical representative I in the same class of the ICM as L, an element x so that L = x*I, the multiplicator ring S, the canonical representative W of its weak equivalence class, and the element g in Pic(S) representing the invertible S-ideal (L:W).}
    S := MultiplicatorRing(L);
    PS, pS := PicardGroup(S);
    wkS := WKICM_barCanonicalRepresentatives(S);
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
    icm_can,icm_lookup:=ICM_CanonicalRepresentatives(R);

    for L in ICM(R) do 
        _:=ICM_Identify(L,icm_lookup);
    end for;

*/
