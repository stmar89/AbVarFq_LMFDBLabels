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
    
    SetVerbose("padictocc",1);
    try 
        printf "starting with %o\n",s;
        P<x>:=PolynomialRing(Integers());
        f:=P!eval(s);
        label:=IsogenyLabel(f);
        file_out:=fld_out cat label cat "_cm.txt";
        if OpenTest(file_out,"r") then
            printf "%o already done\n",label;
            quit;
        end if;

        A:=EtaleAlgebra(f);
        g,q:=DimensionSizeFiniteField(A);
        k:=30;
        go:=false;
        while not go and k lt 10^3 do
            try
                PHI:=pAdicPosCMType(A : precpAdic:=k);
                str:=SaveCMType(PHI);
                fprintf file_out,"%o",str;
                printf "%o: done\n",label;
                go:=true;
            catch e
                k+:=30;
                e;
                printf "increasing precision to %o for %o\n",k,label;
            end try;
        end while;
        if k ge 10^3 then
            quit;
        end if;
    catch e
        printf "*********************************************\n%o\n%o\n", label,e;
        fprintf issues, "*********************************************\n%o\n%o\n", label,e;
    end try;
    quit;

