/* vim: set syntax=magma :*/


declare verbose AllIsogenies,1;

declare attributes AlgEtQOrd: RepresentativeMinimalIsogeniesTo;

intrinsic DistinguishedCosetRep(g::GrpAbElt, H::GrpAb) -> GrpAbElt, GrpAb
{Given an element g and a subgroup H of an ambient abelian group G, finds a canonically chosen representative of g+H (and also returns H itself for convenience).  The output only depends on g+H.}
    if Order(g) eq 1 then
        return g, H;
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
        return best, H;
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


//TODO The code of the next few intrinsic is very complicated (eg many nested for loops). Needs more explaination.

// The following two intrinsics give representative isogenies under the action of Pic(Z[F,V]).  
intrinsic RepresentativeMinimalIsogenies(ZFV::AlgEtQOrd, N::RngIntElt : degrees:=[])->Assoc
{Given the ZFV order of a squarefree isogeny class, it returns an associative array, indexed by the distinguished representatives J of isomorphism classes, in which each entry contains an associative array with data describing isogenies to J. This data consists of a tuple ... 
//TODO finish descr
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
        Ls := MaximalIntermediateIdeals(J, N*J);
        for L in Ls do
            deg := Index(J, L);
            if degrees cmpne [] and not (deg in degrees) then
                continue;
            end if;
            I, x, IS, IWE, Ig := ICM_Identify(L, icm_lookup);
            assert2 Index(J, x*I) eq deg;
            Ig, Ker := DistinguishedCosetRep(Ig@@P0Pmap, Kernel(P0Pmap));
            Append(~min_isog[myHash(IWE)][we_hashes[j]], <deg, x, Ig, Ker, I, L>); // x is a minimal isogeny from I to J of degree deg=#(J/L); I = IWE * Ig as distinguished representatives
        end for;
    end for;
    ZFV`RepresentativeMinimalIsogeniesTo[<N, degrees>] := min_isog;
    return min_isog;
end intrinsic;

intrinsic RepresentativeIsogenies(ZFV::AlgEtQOrd, degree_bounds::SeqEnum)->Assoc
{}
    N := LCM(degree_bounds);
    degrees := {};
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
    for i->I in we_reps do
        hshI := we_hashes[i];
        isog[hshI] := AssociativeArray();
        for j->J in we_reps do
            hshJ := we_hashes[j];
            isog[hshI][hshJ] := AssociativeArray();
            for data in min_isog[hshI][hshJ] do
                d, x, h, H, _, L := Explode(data);
                if not IsDefined(isog[hshI][hshJ], d) then
                    isog[hshI][hshJ][d] := [];
                end if;
                Append(~isog[hshI][hshJ][d], <x, h, H, L>);
            end for;
        end for;
    end for;
    while true do
        added_something := false;
        for i->I in we_reps do
            hshI := we_hashes[i]; projI := we_proj[i];
            SI := MultiplicatorRing(I);
            for j->J in we_reps do
                hshJ := we_hashes[j]; projJ := we_proj[j];
                for k->K in we_reps do
                    hshK := we_hashes[k]; projK := we_proj[k];
                    for m->known in isog[hshK][hshJ] do
                        for yL0 in known do
                            y, g, G, L0 := Explode(yL0);
                            for data in min_isog[hshI][hshK] do
                                d, x, h, H := Explode(data);
                                dm := d*m;
                                if dm in degrees then
                                    gh, GH := DistinguishedCosetRep(g+h, G+H);
                                    I0 := icm_lookup[SI][<I, projI(gh)>];
                                    xy := x*y;
                                    L := (xy) * I0;
                                    if not IsDefined(isog[hshI][hshJ], dm) then
                                        isog[hshI][hshJ][dm] := [<xy, gh, GH, L>];
                                        added_something := true;
                                    else
                                        hsh := myHash(L);
                                        hashes := {myHash(M[4]) : M in isog[hshI][hshJ][dm]};
                                        if not hsh in hashes then
                                            // myHash is collision free
                                            Append(~isog[hshI][hshJ][dm], <xy, gh, GH, L>);
                                            assert2 Index(J, L) eq dm;
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


