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
    SetClassGroupBounds("GRH"); // the cohen-mac type >2 case requirs to compute Pics

    try 
        P<x>:=PolynomialRing(Integers());
        f:=P!eval(s);
        label:=IsogenyLabel(f);
        file_out:=fld_out cat label cat "_wk.txt";

        if not OpenTest(file_out,"r") then
            t0:=Cputime();
            A:=EtaleAlgebra(f);
            g,q:=DimensionSizeFiniteField(A);
            F:=PrimitiveElement(A);
            ZFV:=Order([F,q/F]);
            str:=FillSchemaWEClasses(ZFV);
            fprintf file_out,"%o",str;
            printf "%o: done in %o\n",label,Cputime(t0);
        end if;
    catch e
        printf "*********************************************\n%o\n%o\n", label,e;
        fprintf issues, "*********************************************\n%o\n%o\n", label,e;
    end try;
    quit;

