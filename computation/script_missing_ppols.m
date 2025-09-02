/* vim: set syntax=magma : */
  
    
    done:=Split(Pipe("ls /data/stmar/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_isog/","r"));
    input:=Split(Read("~/AbVarFq_LMFDBLabels/computation/weil_poly_sqfree_ord_cs_no_3_25.txt")) cat 
           Split(Read("~/AbVarFq_LMFDBLabels/computation/weil_poly_sqfree_ord_only_3_25.txt"));
    file_out:="~/AbVarFq_LMFDBLabels/computation/weil_poly_missing_pp_script_with_3_25.txt";

    AttachSpec("~/AbVarFq_LMFDBLabels/spec");
    PP<x>:=PolynomialRing(Integers());
    input_labels:=[ IsogenyLabel(PP!eval(s)) : s in input ];
    missing_labels:=Seqset(input_labels) diff Seqset(done);
    missing_coeffs:=[ Coefficients(f) where _,_,f:=LabelToPoly(ll) : ll in missing_labels ];
    printf "total input = %o\tdone = %o\tmissing = %o\n",#input,#done,#missing_coeffs;

    "printing";
    for cc in missing_coeffs do
        fprintf file_out,"%o\n",cc;
    end for;

    quit;

