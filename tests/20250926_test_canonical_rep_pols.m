/*
    We spotted a bug in ClosestVectors triggering a Magma Internal Error on architectures:
    binary avx2 fails, while avx64 or intel64 works.
    In particular, while on babbage it gives trouble, on kovalevsky seems fine.

    In this test, we recompute on kovalevsky the isomorphism classes of PPAVs for a certain number of isogeny 
    classes previously computed on babbage. Since the reps of the princ polarizations are canonical (and dependent
    on the output of ClosestVectors) we hope to get the exact same elements. If this is not the case, we are in 
    trouble and need to recompute everything.

    USAGE: on kovalevksy
    to prepare the input
        magma -b task:=200 ~/AbVarFq_LMFDBLabels/tests/20250926_test_canonical_rep_pols.m 
    to remove all relevant .sig
        rm ~/AlgEt/AlgEtQ/*.sig
        rm ~/AbVarFq_LMFDBLabels/packages/*.sig
    to run the parallel (current version of magma)
        ls ~/292_test_canonical_rep_pols/from_babbage | parallel -j 20 magma -b task:={} ~/AbVarFq_LMFDBLabels/tests/20250926_test_canonical_rep_pols.m
    to run the parallel (older version of magma)
        ls ~/292_test_canonical_rep_pols/from_babbage | parallel -j 20 /opt/magma/magma-2.28-15/magma -b task:={} ~/AbVarFq_LMFDBLabels/tests/20250926_test_canonical_rep_pols.m
    to run the parallel (current version of magma), only specific examples
        parallel -j 20 magma -b task:={} ~/AbVarFq_LMFDBLabels/tests/20250926_test_canonical_rep_pols.m ::: 4.3.c_e_k_o 4.4.c_c_ac_d 4.4.f_g_ar_acp 4.4.ae_g_am_bh 


*/

    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AbVarFq_LMFDBLabels/spec");
    // import "~/AbVarFq_LMFDBLabels/computation/script_pols.m" : print_ivec;
    // causing troubles...copied the function below...go figure...
    SetClassGroupBounds("GRH");
    SetColumns(0);
    _<x>:=PolynomialRing(Integers());

    fld:="~/292_test_canonical_rep_pols/"; // on kovalevsky
    babbage_outputs:=fld * "from_babbage/";
    av_fq_pol_columns := ["label", "isog_label", "endomorphism_ring", "isom_label", "degree", "kernel", "degree_rr", "kernel_rr", "degree_rl", "kernel_rl", "degree_lr", "kernel_lr", "degree_ll", "kernel_ll", "aut_group", "geom_aut_group", "is_jacobian", "representative"];
    file_output_test:=fld * "output_of_test";

    function print_ivec(v : json:=false)
        base := json select "[%o]" else "{%o}";
        if Type(v) eq SeqEnum or Type(v) eq Tup then
            return Sprintf(base, Join([$$(c : json:=json) : c in v], ","));
        end if;
        return Sprint(v);
    end function;

    is_tot_pos:=function(x)
        xb:=ComplexConjugate(x);
        if not x eq xb then 
            return false;
        end if;
        homs:=HomsToC(Algebra(x));
        return forall{phi:phi in homs|Re(phi(x)) gt 0};
    end function;

    prep_input:=procedure(N)
        // we clear out the folder
        if StringToInteger(Pipe("ls " cat babbage_outputs cat " |wc -l","r")) ne 0 then
            Pipe("rm " cat babbage_outputs cat "*","r");
        end if;
        assert StringToInteger(Pipe("ls " cat babbage_outputs cat " |wc -l","r")) eq 0;

        // we pick N randomly selected elements from 
        Pipe("ssh stmar@babbage.mit.edu 'find /data/stmar/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_pol -type f -print0 | shuf -z -n" * Sprint(N) * " | xargs -0 -r -I '{}' scp '{}' stmar@kovalevsky.mit.edu:~/292_test_canonical_rep_pols/from_babbage/'","r");
        assert StringToInteger(Pipe("ls " cat babbage_outputs cat " | wc -l","r")) eq StringToInteger(N);
    end procedure;

    parallel_script:=procedure(label)
        recomputed := {};
        original0 := Split(Read(babbage_outputs * label)); //from babbage
        original:= {};
        // we gt rig of the geom_aut_group stuff
        for line in original0 do
            sp:=Split(line,":");
            sp[16]:="\\N";
            Include(~original,Join(sp,":"));
        end for;

            
      
        t0:=Cputime();
        g,q,f:=LabelToPoly(label);
        A:=EtaleAlgebra(f);
        F:=PrimitiveElement(A);
        ZFV:=LoadSchemaWKClasses(FillSchemaWEClasses(Order([F,q/F])));
        A:=Algebra(ZFV);
        F:=PrimitiveElement(A);
        // Need to make sure that the cm-type is the same.
        // each polarization determines uniquely the cm-type.
        // I pick one from original and use it.
        PHI:=sp[#sp] where sp:=Split(Random(original),":");
        PHI:=[StringToInteger(z):z in Split(PHI,"[],")];
        PHI:=DotProduct(ZFVBasis(A),[PHI[i]/PHI[1]:i in [2..#PHI]]);
        A`pAdicPosCMType:=CMType(PHI);

        for ppol in PPolIteration(ZFV) do
            poldata := AssociativeArray();
            we, pic_ctr, I, den, nums, lambda, label_pol := Explode(ppol);
            assert is_tot_pos(lambda/PHI);
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
            // if geom_endalg_is_comm then
            //     poldata["geom_aut_group"] := aut_grp;
            // else
                poldata["geom_aut_group"] := "\\N";
            // end if;
            poldata["is_jacobian"] := IsProductOfOrdersLMFDB(S) select "f" else "\\N";
            poldata["representative"] := Sprintf("[%o,%o]", den, print_ivec(nums: json:=true));
            Include(~recomputed,Join([poldata[col] : col in av_fq_pol_columns], ":"));
        end for;
        t1:=Cputime(t0);

        // test and print outcome
        if recomputed eq original then
            fprintf file_output_test,"OK in %o %o\n",t1,label;
            printf "OK in %o %o\n",t1,label;
        else
            fprintf file_output_test,"ERROR -------------> %o\n####\nold minus new:\n%o\n####\nnew minus old\n%o\n#########################################################\n",label,
            Join(Sort(Setseq(original diff recomputed)),"\n"),
            Join(Sort(Setseq(recomputed diff original)),"\n");
            printf "ERROR -------------> %o\n####\nold minus new:\n%o\n####\nnew minus old\n%o\n#########################################################\n",label,
            Join(Sort(Setseq(original diff recomputed)),"\n"),
            Join(Sort(Setseq(recomputed diff original)),"\n");
        end if;
    end procedure;


    // task is a string containing either an integer or an LMFDB label.
    sp:=#Split(task,".");
    if sp eq 3 then
        parallel_script(task);
    elif sp eq 1 then
        prep_input(task);
    else
        error "the input variable task is not of an accepted format: it should be either an integer or a label";
    end if;
    
    quit;

