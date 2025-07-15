/* vim: set syntax=magma :*/

/*
    variables:
        issues              # we collect here the issues
        fld_comp            # where the computation is running
        fld_out_wk          # output folder of wk script
        fld_out_cm          # output folder of cm script
        fld_out_pols        # output folder for this script
        s = string of integers, eg [ 101, -20, 1 ] 
        degree_bounds = string of square integers, eg [ 4, 9, 25 ] 
*/

/* // assignements for debugging. make sure to not fprint anything!
    fld_comp:="~/287_abvarfq_lmfdb_recomputation/";
    fld_out_wk:="~/287_abvarfq_lmfdb_recomputation/output_wk/";
    fld_out_cm:="~/287_abvarfq_lmfdb_recomputation/output_cm/";
    fld_out_pols:="~/287_abvarfq_lmfdb_recomputation/output_pols/";
    degree_bounds:="[4,9,25]";
    s:="[64,-80,44,-19,11,-5,1]"; //3.4.af_l_at
    s:="[961,-62,-29,-2,1]"; //2.31.ac_abd
*/
/*

To compute:
* av_fq_pol: 
    label,              -- label of polarization, of the form g.q.coefffs-N.i.w.j-d.k)
    isog_label,         -- g.q.coeffs
    endomorphism_ring,  -- N.i
    isom_label,         -- w.j
    degree,             -- d 
    kernel,
    degree_rr,
    kernel_rr,
    degree_rl,
    kernel_rl,
    degree_lr,
    kernel_lr,
    degree_ll,
    kernel_ll,
    aut_group, 
    geom_aut_group (can say that it is equal to aut_group when End^0(Fqbar) is commutative; 
                   can check this from av_fq_endalg_data->divalg_dim for each factor in av_fq_endalg_factors), 
    is_jacobian (say false if a product at all, none otherwise)
    representative

* av_fq_weak_equivalences: 
    label (for matching), 
    pic_invs, 
    pic_basis, 
    is_product, 
    product_partition, 
    is_conjugate_stable, 
    generator_over_ZFV, 
    is_Zconductor_sum
    is_ZFVconductor_sum

* av_fq_isog: 
    pic_prime_gens,
    size

* allproduct: if IsProductOfOrdersLMFDB is true for all orders, we record the number of princ polarizations
                //is this info in some table?
                //NO: it was supposed to be used as a test:
                //    if everything is a product then the polarizations are so as well.

*/

//AttachSpec("~/CHIMP/CHIMP.spec");
AttachSpec("~/AlgEt/spec");
AttachSpec("~/AbVarFq_LMFDBLabels/spec");
SetClassGroupBounds("GRH");
SetColumns(0);
//SetDebugOnError(true);

PP<x>:=PolynomialRing(Integers());
h:=PP!eval(s);
label:=IsogenyLabel(h);
split:=Split(label,".");
g:=eval(split[1]);
q:=eval(split[2]);
_,p:=IsPrimePower(q);
is_ordinary:=IsCoprime(Coefficients(h)[(Degree(h) div 2)+1], p);

av_fq_pol_output := Sprintf("%oav_fq_pol/%o", fld_out_pols, label);
av_fq_we_output := Sprintf("%oav_fq_we/%o", fld_out_pols, label);
av_fq_isog_output := Sprintf("%oav_fq_isog/%o", fld_out_pols, label);
allproduct_output := Sprintf("%oallproduct/%o", fld_out_pols, label);
cmfile := Sprintf("%o_cm.txt", fld_out_cm * label);
degree_bounds := eval(degree_bounds);

// early exit if already done
if OpenTest(av_fq_isog_output,"r") then
    quit;
end if;

av_fq_we_columns := ["label", "pic_invs", "pic_basis", "is_product", "product_partition", "is_conjugate_stable", "generator_over_ZFV", "is_Zconductor_sum", "is_ZFVconductor_sum"];

av_fq_isog_columns := ["pic_prime_gens","size"];

av_fq_pol_columns := ["label", "isog_label", "endomorphism_ring", "isom_label", "degree", "kernel", "degree_rr", "kernel_rr", "degree_rl", "kernel_rl", "degree_lr", "kernel_lr", "degree_ll", "kernel_ll", "aut_group", "geom_aut_group", "is_jacobian", "representative"];

function print_ivec(v : json:=false)
    base := json select "[%o]" else "{%o}";
    if Type(v) eq SeqEnum or Type(v) eq Tup then
        return Sprintf(base, Join([$$(c : json:=json) : c in v], ","));
    end if;
    return Sprint(v);
end function;

// we start by loading the data that was already computed,
// including commutative_geom_endalg data
try
    commlines := Split(Read(Sprintf("%ocommutative_geom_endalg/%o.%o", fld_comp, g, q)), "\n");
    ZFV := LoadSchemaWKClasses(Read(Sprintf("%o_wk.txt", fld_out_wk * label)));
    A := Algebra(ZFV);
    if is_ordinary then
        assert OpenTest(cmfile, "r");
        cmdata := Read(cmfile);
        PHI := LoadpAdicPosCMType(A, cmdata);
        assert assigned A`pAdicPosCMType;
    else
        PHI:=""; //to avoid an error
    end if;
catch e
    printf "*********************************************\nmissing some precomputed data for %o\n%o\n", label,e;
    fprintf issues, "*********************************************\nmissing some precomputed data%o\n%o\n", label,e;
end try;

try
    t0:=Cputime();
    allproduct := true;
    geom_endalg_is_comm := 0;
    for line in commlines do
        llabel, iscomm := Explode(Split(line, " "));
        if label eq llabel then
            geom_endalg_is_comm := (iscomm[1] eq "t");
            break;
        end if;
    end for;
    assert geom_endalg_is_comm cmpne 0;
    av_fq_pol := [];
    av_fq_we := [];
    av_fq_isog := AssociativeArray();
    _, cangens := DistinguishedPicGenerators(ZFV);
    _ := DistinguishedPicBases(ZFV); // sets DistinguishedPicBasis for each S
    av_fq_isog["pic_prime_gens"] := print_ivec(cangens);
    isogeny_size:=0;
    for S in OverOrders(ZFV) do
        Pbasis, construction := DistinguishedPicBasis(S);
        invs, construction := Explode(construction);
        Sdata := AssociativeArray();
        Sdata["label"] := WELabel(S);
        Sdata["pic_invs"] := print_ivec(invs);
        Sdata["pic_basis"] := print_ivec(construction);
        product, _, partition := IsProductOfOrdersLMFDB(S);
        allproduct := allproduct and product;
        Sdata["is_product"] := product select "t" else "f";
        Sdata["product_partition"] := print_ivec(partition: json:=true);
        Sdata["is_conjugate_stable"] := IsConjugateStable(S) select "t" else "f";
        _, dens, nums := SmallestMonogenicGeneratorOverZFV(S, ZFV);
        if #dens eq 0 then
            Sdata["generator_over_ZFV"] := "\\N";
        else
            Sdata["generator_over_ZFV"] := Sprintf("[%o,%o]", dens[1], print_ivec(nums[1] : json:=true));
        end if;
        Sdata["is_Zconductor_sum"] := (S eq Order(ZBasis(Conductor(S)))) select "t" else "f";
        Sdata["is_ZFVconductor_sum"] := (S eq Order(ZBasis(Conductor(S)) cat ZBasis(ZFV))) select "t" else "f";
        assert assigned S`WKICM_bar;
        assert assigned S`PicardGroup;
        isogeny_size +:= #WKICM_bar(S) * #PicardGroup(S);
        Append(~av_fq_we, Sdata);
    end for;
    av_fq_isog["size"] := Sprint(isogeny_size);
    if is_ordinary then
        for ppol in PPolIteration(ZFV) do
            poldata := AssociativeArray();
            we, pic_ctr, I, den, nums, lambda, label_pol := Explode(ppol);
            S := MultiplicatorRing(I);
            split_we:=Split(we, "-");
            assert split_we[1] eq label;
            pieces := Split(split_we[2],"."); //N i w
            poldata["label"] := label_pol; //label of the polarization
            poldata["isog_label"] := label;
            poldata["endomorphism_ring"] := Join(pieces[1..2], "."); //N.i
            poldata["isom_label"] := Sprintf("%o.%o", pieces[3], pic_ctr); //w.j
            poldata["degree"] := "1";
            Iv:=TraceDualIdeal(ComplexConjugate(I));
            kerinfo:=DecompositionKernelOfIsogeny(I,Iv,lambda);
            FillKernelInfo(~poldata, kerinfo);
            aut_grp := IdentifyGroup(TorsionSubgroup(UnitGroup(S)));
            aut_grp := Sprintf("%o.%o", aut_grp[1], aut_grp[2]);
            poldata["aut_group"] := aut_grp;
            if geom_endalg_is_comm then
                poldata["geom_aut_group"] := aut_grp;
            else
                poldata["geom_aut_group"] := "\\N";
            end if;
            poldata["is_jacobian"] := IsProductOfOrdersLMFDB(S) select "f" else "\\N";
            poldata["representative"] := Sprintf("[%o,%o]", den, print_ivec(nums: json:=true));
            Append(~av_fq_pol, poldata);
        end for;
        number_of_princ_pols:=#av_fq_pol;
//        for I->Ipols in AllNonprincipalPolarizations(ZFV, PHI, degree_bounds) do
//            S := MultiplicatorRing(I);
//            aut_grp := IdentifyGroup(TorsionSubgroup(UnitGroup(S)));
//            aut_grp := Sprintf("%o.%o", aut_grp[1], aut_grp[2]);
//            isom_label_split:=Split(I`IsomLabel,"-");
//            assert isom_label_split[1] eq label;
//            pieces := Split(isom_label_split[2], "."); //[N,i,w,j]
//            for d->Idpols in Ipols do
//                for data in Idpols do
//                    pol, den, nums, kerinfo , label_pol:= Explode(data);
//                    poldata := AssociativeArray();
//                    poldata["label"] := label_pol;
//                    poldata["isog_label"] := label;
//                    poldata["endomorphism_ring"] := Join(pieces[1..2], ".");
//                    poldata["isom_label"] := Join(pieces[3..4],".");
//                    poldata["degree"] := Sprint(d);
//                    FillKernelInfo(~poldata, kerinfo);
//                    poldata["aut_group"] := aut_grp;
//                    if geom_endalg_is_comm then
//                        poldata["geom_aut_group"] := aut_grp;
//                    else
//                        poldata["geom_aut_group"] := "\\N";
//                    end if;
//                    poldata["is_jacobian"] := "f";
//                    poldata["representative"] := Sprintf("[%o,%o]", den, print_ivec(nums: json:=true));
//                    Append(~av_fq_pol, poldata);
//                end for;
//            end for;
//         end for;
    end if;

    // we print all outputs
    if is_ordinary and allproduct then
        fprintf allproduct_output, "%o\n", number_of_princ_pols;
    end if;
    for pol_line in av_fq_pol do
        fprintf av_fq_pol_output, "%o\n", Join([pol_line[col] : col in av_fq_pol_columns], ":");
    end for;
    for we_line in av_fq_we do
        fprintf av_fq_we_output, "%o\n", Join([we_line[col] : col in av_fq_we_columns], ":");
    end for;
    fprintf av_fq_isog_output, "%o\n", Join([av_fq_isog[col] : col in av_fq_isog_columns], ":");
    printf "%o : done in %o\n",label,Cputime(t0); 
catch e
    printf "*********************************************\n%o\n%o\n", label,e;
    fprintf issues, "*********************************************\n%o\n%o\n", label,e;
end try;
quit;
