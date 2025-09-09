/* vim: set syntax=magma : */
  
    
    done:=Split(Pipe("ls /data/stmar/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_isog/","r"));
    input:=Split(Read("~/AbVarFq_LMFDBLabels/computation/weil_poly_sqfree_ord_cs_no_3_25.txt")) cat 
           Split(Read("~/AbVarFq_LMFDBLabels/computation/weil_poly_sqfree_ord_only_3_25.txt"));
    file_out:="~/AbVarFq_LMFDBLabels/computation/weil_poly_missing_pp_script_with_3_25.txt";

    AttachSpec("~/AbVarFq_LMFDBLabels/spec");
    PP<x>:=PolynomialRing(Integers());
    input_labels:=[ IsogenyLabel(PP!eval(s)) : s in input ];
    missing_labels:=Setseq(Seqset(input_labels) diff Seqset(done));
    // we sort putting 4.4, 4.3, 5.2, 3.16, 3.25 at the end, in this order.
    missing_labels:=[
        [ l : l in missing_labels | Join(Split(l,".")[1..2],".") notin { "4.4","4.3","5.2","3.16","3.25" }],
        [ l : l in missing_labels | Join(Split(l,".")[1..2],".") eq "4.4" ],
        [ l : l in missing_labels | Join(Split(l,".")[1..2],".") eq "4.3" ],
        [ l : l in missing_labels | Join(Split(l,".")[1..2],".") eq "5.2" ],
        [ l : l in missing_labels | Join(Split(l,".")[1..2],".") eq "3.16" ],
        [ l : l in missing_labels | Join(Split(l,".")[1..2],".") eq "3.25" ]
    ];
    printf "missing = %o\n",[#c:c in missing_labels];
    missing_labels:=&cat(missing_labels);
    missing_coeffs:=[ Coefficients(f) where _,_,f:=LabelToPoly(ll) : ll in missing_labels ];
    printf "total input = %o\tdone = %o\tmissing = %o\n",#input,#done,#missing_coeffs;

    "printing";
    for cc in missing_coeffs do
        fprintf file_out,"%o\n",cc;
    end for;

    quit;

