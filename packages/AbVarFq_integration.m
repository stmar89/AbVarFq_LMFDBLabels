/* vim: set syntax=magma : */
/*
    We include here intrinsics that allow to compute the isomorphism classes of AbVarFq with LMFDB-labels.
*/

declare attributes IsogenyClassFq : IsomorphismClassesLMFDB;
declare attributes AbelianVarietyFq : LMFDBLabel;

intrinsic LMFDBLabel(A::AbelianVarietyFq)->MonStgElt
{Return the LMFDB label of the abelian variety.}
    require assigned A`LMFDBLabel : "The label is not assigned. Run first IsomorphismClassesLMFDB\n";
    return A`LMFDBLabel;
end intrinsic;

intrinsic LMFDBLabel(S::AlEtQOrd)->MonStgElt
{Return the LMFDB label of the endomorphism ring.}
    require assigned S`LMFDBLabel : "The label is not assigned. Run first IsomorphismClassesLMFDB\n";
    return S`WELabel;
end intrinsic;

intrinsic IsomorphismClassesLMFDB(AVh::IsogenyClassFq)->SeqEnum[AbelianVarietyFq]
{Computes a list of representatives of isomorphisms classes of abelian varieties in the given isogeny class, together with their LMFDB labels.}
    if not assigned AVh`IsomorphismClassesLMFDB then
        require  IsSquarefree(AVh) and (IsOrdinary(AVh) or IsCentelegheStix(AVh)): "Implemented only for isogogeny classes with commutative endomorphism algebra which are ordinary or over Fp.\n";
        _,map:=DeligneAlgebra(AVh);
        ZFV:=ZFVOrder(AVh);
        isom_DMs:=ICM_DistinguishedRepresentatives(ZFV);
        isom_AVs:=[];
        for I in isom_DMs do
            M:=ModuleFromDirectSum(ZFV,map,[<I,map>]);
            A:=AbelianVarietyFromDeligneModule(AVh,M);
            A`LMFDBLabel:=I`IsomLabel;
            Append(~isom_AVs,A);
        end for;
    end if;
    AVh`IsomorphismClassesLMFDB:=isom_AVs;
    if assigned AVh`IsomorphismClasses then
        printf "Warning: replacing the previously computed representatives of the isomorphism classes with the LMDFB distinguished ones.\n";
    end if;
    AVh`IsomorphismClasses := AVh`IsomorphismClassesLMFDB;
    return AVh`IsomorphismClassesLMFDB;
end intrinsic;

