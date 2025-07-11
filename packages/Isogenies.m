/* vim: set syntax=magma :*/


declare verbose AllIsogenies,1;

declare attributes AlgEtQOrd: RepresentativeMinimalIsogeniesTo;

intrinsic DistinguishedCosetRep(g::GrpAbElt, H::GrpAb) -> GrpAbElt
{Given an element g and a subgroup H of an ambient abelian group G, finds a canonically chosen representative of g+H.  The output only depends on g+H.}
    if Order(g) eq 1 then
        return g;
    end if;
    G := Parent(g);
    if (#H)^2 le #G then
        // iterate over H and find the smallest element
        best := g; first := Eltseq(g);
        for h in H do
            eh := Eltseq(h);
            if eh lt first then
                best := h;
                first := eh;
            end if;
        end for;
        return best;
    else
        // iterate over G until you find an element of g+H
        for h in G do
            // iterating over abelian groups happens in a strange order, but that's okay for us as long as it's consistent.
            if h - g in H then
                return h;
            end if;
        end for;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The following two intrinsics give representative isogenies under the action of Pic(Z[F,V]):
// 
// More precisely, the philosophy behind is that if J is an ideal with (J:J)=S, N is a positive integer and 
// I is an invertible S-ideal then there is an S-linear bijection between
// J/NJ <--> JI/NJI,
// which sends an ideal L such that NJ < L < J with no L' such that L < L' < J 
// to a submodule LI satisfying the same property wrt to JI.
// In other words, it sensds maximal subideals of J contaninig NJ to maximal subideals of JI containing NJI.
// This implies that the minimal isogenies to J are in bijection with the minimal isogenies to JI.
// 
// The upshot is that to compute isogenies of bounded degrees (by composing minimal ones) we only need 
// to loop over the weak equivalence classes, instead of all the isomorphism classes.
//
// Since we are not storing Pic(S), but only Pic(ZFV) and the extension maps, we need to keep track of a bunch
// of additional information to be able to use these bijections. This explainins 
////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic RepresentativeMinimalIsogenies(ZFV::AlgEtQOrd, N::RngIntElt : degrees:=[])->Assoc
{Given the ZFV order of a squarefree isogeny class, it returns an associative array, indexed by the distinguished representatives J of isomorphism classes, in which each entry contains an associative array with data describing isogenies to J. This data consists of a tuple <deg, x, Ig, Ker, I, L> where
- deg is the degree of the isogeny
- x is an element representing the isogeny, ie x*I < J.
- Ig is an element of Pic(ZFV) mapping to (x*I : W) where W is the distinguished rep of the weak equivalence class of I
- Ker is the kernel of Pic(ZFV) -> Pic(S), where S is the endomorphism ring of J
- I is the domain of the isogeny (the distinguished rep of the weak equivalence class)
- L is x*I, the image of the isogeny
}
    if not assigned ZFV`RepresentativeMinimalIsogeniesTo then
        ZFV`RepresentativeMinimalIsogeniesTo := AssociativeArray();
    end if;
    if IsDefined(ZFV`RepresentativeMinimalIsogeniesTo, <N, degrees>) then
        return ZFV`RepresentativeMinimalIsogeniesTo[<N, degrees>];
    end if;
    if not assigned ZFV`DistinguishedPicBases then
        _ := DistinguishedPicBases(ZFV);
    end if;
    isom_cl, icm_lookup := ICM_DistinguishedRepresentatives(ZFV);
    // It should be possible to implement this function without enumerating the whole ICM, but instead just enumerating weak equivalence classes.
    // But we need to call ICM_Identify, which currently relies on the lookup table constructed in ICM_DistinguishedRepresentatives, so we don't try to do this now.
    min_isog := AssociativeArray();
    we_reps := &cat[[icm_lookup[S][<WE, P.0>] : WE in WKICM_barDistinguishedRepresentatives(S) ] where P := PicardGroup(S) : S in OverOrders(ZFV)];
    we_hashes := [myHash(J) : J in we_reps];
    // min_isog[I][J] will be the minimal isogenies from I to J
    for i->I in we_reps do
        min_isog[we_hashes[i]] := AssociativeArray();
        for j->J in we_reps do
            min_isog[we_hashes[i]][we_hashes[j]] := [];
        end for;
    end for;
    for j->J in we_reps do
        S := MultiplicatorRing(J);
        P := PicardGroup(S);
        _, _, P0Pmap := DistinguishedPicBasis(S);
        // P0Pmap: Pic(ZFV) -> Pic(S)
        Ls := MaximalIntermediateIdeals(J, N*J);
        // These are ideals L with N*J < L < J, and no L' with L < L' < J.
        for L in Ls do
            deg := Index(J, L);
            if degrees cmpne [] and not (deg in degrees) then
                continue;
            end if;
            I, x, IS, IWE, Ig := ICM_Identify(L, icm_lookup);
            // I : distinguished rep of L
            // x : L=x*I
            // IWE : we class of L
            // Ig : (L:IWE)@@pS where S:=(I:I)
            _, _, P0PISmap := DistinguishedPicBasis(IS);
            assert Index(J, x*I) eq deg;
            // We store isogenies in terms of ideals of ZFV, but Ig is an element of Pic(S).  To get it back into Pic(ZFV), we need to pick a representative in Pic(ZFV) that maps to it.  To do so, we use DistinguishedCosetRep.
            Ker := Kernel(P0PISmap);
            Ig := DistinguishedCosetRep(Ig@@P0PISmap, Ker);
            Append(~min_isog[myHash(IWE)][we_hashes[j]], <deg, x, Ig, Ker, I, L>); // x is a minimal isogeny from I to J of degree deg=#(J/L); I = IWE * Ig as distinguished representatives
        end for;
    end for;
    ZFV`RepresentativeMinimalIsogeniesTo[<N, degrees>] := min_isog;
    return min_isog;
end intrinsic;

intrinsic RepresentativeIsogenies(ZFV::AlgEtQOrd, degree_bounds::SeqEnum)->Assoc
{
Returns an associative array isog so that isog[myHash(I)][myHash(J)][d] is a sequence of all isogenies from I to J of degree d.  Here I and J loop over the distinguished representatives of the weak equivalence classes of ZFV, and d>1 loops over divisors of elements of degree_bounds.  Note that, if no such isogeny exists the key d is not assigned (rather than being an empty sequence).
The value of isog[I][J][d] is a sequence of tuples <x, h, H, L>, where
- x is an element representing the isogeny, ie x*I < J.
- h is an element of Pic(ZFV) mapping to (x*I : W) where W is the distinguished rep of the weak equivalence class of I
- H in the kernel of Pic(ZFV) -> Pic(S), where S is the endomorphism ring of J
- L is x*I, the image of the isogeny
}
    N := LCM(degree_bounds);
    degrees := {};
    // construct the set of nontrivial divisors of the elements in degree_bounds
    for B in degree_bounds do
        for d in Divisors(B) do
            if d eq 1 then continue; end if;
            Include(~degrees, d);
        end for;
    end for;
    t0:=Cputime();
    min_isog := RepresentativeMinimalIsogenies(ZFV, N : degrees:=degrees);
    vprintf AllIsogenies : "time spent on AllMinimalIsogenies %o\n",Cputime(t0);
    isog := AssociativeArray();
    isom_cl, icm_lookup :=ICM_DistinguishedRepresentatives(ZFV);
    we_reps := &cat[[icm_lookup[S][<WE, P.0>] : WE in WKICM_barDistinguishedRepresentatives(S) ] where P := PicardGroup(S) : S in OverOrders(ZFV)];
    we_hashes := [myHash(J) : J in we_reps];
    we_proj := &cat[[P0Pmap where _,_,P0Pmap := DistinguishedPicBasis(S) : WE in WKICM_barDistinguishedRepresentatives(S) ] : S in OverOrders(ZFV)];
    isog := AssociativeArray();
    // We initialize the output isog using minimal isogenies computed by RepresentativeMinimalIsogenies
    for i->WI in we_reps do
        hshWI := we_hashes[i];
        isog[hshWI] := AssociativeArray();
        for j->WJ in we_reps do
            hshWJ := we_hashes[j];
            isog[hshWI][hshWJ] := AssociativeArray();
            for data in min_isog[hshWI][hshWJ] do
                d, x, h, H, I, L := Explode(data);
                // x*I = L c WJ with d=[WJ:I]
                // I~L~WI (wk eq)
                // I = WI*h as isom classes
                if not IsDefined(isog[hshWI][hshWJ], d) then
                    isog[hshWI][hshWJ][d] := [];
                end if;
                Append(~isog[hshWI][hshWJ][d], <x, h, H, L>);
            end for;
        end for;
    end for;
    // We add to isog all possible compositions with degree in degrees.
    while true do
        added_something := false;
        for i->WI in we_reps do
            hshWI := we_hashes[i]; projWI := we_proj[i];
            S := MultiplicatorRing(WI);
            SWI:=S!!WI;
            for j->WJ in we_reps do
                hshWJ := we_hashes[j]; projWJ := we_proj[j];
                for k->WK in we_reps do
                    hshWK := we_hashes[k]; projWK := we_proj[k];
                    for m->known in isog[hshWK][hshWJ] do
                        for yL0 in known do
                            y, g, G, L0 := Explode(yL0);
                            for data in min_isog[hshWI][hshWK] do
                                d, x, h, H := Explode(data);
                                dm := d*m;
                                if dm in degrees then
                                    GH := G + H;
                                    gh := DistinguishedCosetRep(g+h, GH);
                                    I0 := icm_lookup[S][<SWI, projWI(gh)>];
                                    xy := x*y;
                                    L := (xy) * I0;
                                    if not IsDefined(isog[hshWI][hshWJ], dm) then
                                        isog[hshWI][hshWJ][dm] := [<xy, gh, GH, L>];
                                        added_something := true;
                                    else
                                        hsh := myHash(L);
                                        hashes := {myHash(M[4]) : M in isog[hshWI][hshWJ][dm]};
                                        if not hsh in hashes then
                                            // myHash is collision free
                                            Append(~isog[hshWI][hshWJ][dm], <xy, gh, GH, L>);
                                            assert Index(WJ, L) eq dm; //TODO is this correct?
                                            added_something := true;
                                        end if;
                                    end if;
                                end if;
                            end for;
                        end for;
                    end for;
                end for;
            end for;
        end for;
        if not added_something then
            break;
        end if;
    end while;
    return isog;
end intrinsic;

/* TESTS
    TODO Add tests. Some ideas:
        For AllIsogenies: - compute some output using slow naive numeration process of sublattices of the dual variety.
                              - Compare with Example 7.2 in https://arxiv.org/abs/1805.10223
                                f := x^4 + 2*x^3 - 7*x^2 + 22*x + 121;
                              - not sure what to do for minimal isogenies...maybe compute some 
                                for elliptic curves and check for volcanoes?
*/


