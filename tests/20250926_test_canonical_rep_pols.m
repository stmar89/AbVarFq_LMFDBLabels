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
    to run the parallel
        ls ~/292_test_canonical_rep_pols/from_babbage | parallel -j 20 magma -b task:={} ~/AbVarFq_LMFDBLabels/tests/20250926_test_canonical_rep_pols.m
*/

    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AbVarFq_LMFDBLabels/spec");
    import "~/AbVarFq_LMFDBLabels/computation/script_pols.m" : print_ivec;
    SetClassGroupBounds("GRH");
    SetColumns(0);
    _<x>:=PolynomialRing(Integers());

    fld:="~/292_test_canonical_rep_pols/"; // on kovalevsky
    babbage_outputs:=fld * "from_babbage/";
    av_fq_pol_columns := ["label", "isog_label", "endomorphism_ring", "isom_label", "degree", "kernel", "degree_rr", "kernel_rr", "degree_rl", "kernel_rl", "degree_lr", "kernel_lr", "degree_ll", "kernel_ll", "aut_group", "geom_aut_group", "is_jacobian", "representative"];
    file_output_test:=fld * "output_of_test";

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
            fprintf file_output_test,"ERROR -------------> %o\n",label;
            printf "ERROR -------------> %o\n",label;
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

