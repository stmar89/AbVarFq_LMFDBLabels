/* vim: set syntax=magma : */
/*
    variables:
        issues       # we collect here the issue from the weak eq script
        fld_out      # output folder
        s = string of integers, eg [ 101, -20, 1 ] 
*/
    
    AttachSpec("~/CHIMP/CHIMP.spec");
    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AbVarFq_LMFDBLabels/spec");

    try 
        P<x>:=PolynomialRing(Integers());
        f:=P!eval(s);
        A:=EtaleAlgebra(f);
        g,q:=DimensionSizeFiniteField(A);
        PHI:=pAdicPosCMType(A);
        str:=SaveCMType(PHI);

        label:=IsogenyLabel(f);
        file_out:=fld_out cat label cat "_cm.txt";
        fprintf file_out,"%o",str;
        printf "%o: done\n",label;
    catch e
        printf "*********************************************\n%o\n%o\n", label,e;
        fprintf issues, "*********************************************\n%o\n%o\n", label,e;
    end try;
    quit;

