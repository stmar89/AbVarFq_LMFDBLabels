/* vim: set syntax=magma :*/

/*
    variables:
        issues              # we collect here the issues
        fld_comp            # where the computation is running
        fld_out_wk          # output folder of wk script
        fld_out_sing_primes # output folder of this computation
        s = string of integers, eg [ 101, -20, 1 ] 
*/

/* // assignements for debugging. make sure to not fprint anything!
    fld_comp:="~/287_abvarfq_lmfdb_recomputation/";
    fld_out_wk:="~/287_abvarfq_lmfdb_recomputation/output_wk/";
    s:="[64,-80,44,-19,11,-5,1]"; //3.4.af_l_at
    s:="[961,-62,-29,-2,1]"; //2.31.ac_abd
*/
/*

To compute:
* av_fq_isog:
    label_isog              # for matching, of format g.q.coeffs
    singular_primes         # text[], a list of strings describing the singular ideal ideals, sorted using 
                            # SortPrimes
                            # eg. ["2,1/8*(1 + 129*F - 501*V + 7*F^2)", "5, 1/5*(1 + 3F)", "5,1/25*(2+5*F + F^2)"]
* av_fq_weak_equivalences: 
    label_we                # for matching, of format g.q.coeffs.N.i.w
    singular_support        # \\N unless the we class is an order
                            # 0 for Z[F,V]
                            # base codification of a sting of binary bits where ith vlaues is 1 
                            # precisely when (Z[F,V]:S) has support at the ith singular_primes 

*/

AttachSpec("~/CHIMP/CHIMP.spec");
AttachSpec("~/AlgEt/spec");
AttachSpec("~/AbVarFq_LMFDBLabels/spec");
SetClassGroupBounds("GRH");
SetColumns(0);
//SetDebugOnError(true);

PP<x>:=PolynomialRing(Integers());
h:=PP!eval(s);
label_isog:=IsogenyLabel(h);
split:=Split(label_isog,".");
g:=eval(split[1]);
q:=eval(split[2]);

av_fq_we_output := Sprintf("%oav_fq_we/%o", fld_out_pols, label_isog);
av_fq_isog_output := Sprintf("%oav_fq_isog/%o", fld_out_pols, label_isog);

// early exit if already done
if OpenTest(av_fq_isog_output,"r") then
    quit;
end if;


// we start by loading the data that was already computed
try
    str_we:=Read(Sprintf("%o_wk.txt", fld_out_wk * label_isog));
    ZFV := LoadSchemaWKClasses(str_we);
    A := Algebra(ZFV);
catch e
    printf "*********************************************\nmissing some precomputed data for %o\n%o\n", label,e;
    fprintf issues, "*********************************************\nmissing some precomputed data%o\n%o\n", label,e;
end try;

try
    assert assigned ZFV`WKICM;
    ss:=SortSingularPrimes(ZFV);
    singular_primes:=[];
    for P in ss do
        _,str:=SmallMinimalGensPrimeZFV(P);
        Append(~singular_primes,"\"" * RemoveBlanks(Join(str,",")) * "\"");
    end for;
    singular_primes:="[" * Join(singular_primes,",") * "]";

    av_fq_isog := label_isog * ":" * singular_primes;

    av_fq_we := [];
    wk:=WKICM(ZFV);
    assert forall{I:I in wk|assigned I`WELabel};
    for I in wk do
        label_we:=WELabel(I); //g.q.coeff-N.i.w
        w:=Split(label_we,".");
        w:=w[#w];
        is_order:=w eq "1";
        if is_order then
            S:=MultiplicatorRing(I);
            assert OneIdeal(S) eq S!!I;
            assert assigned S`WELabel;
            rel_cond:=ColonIdeal(OneIdeal(ZFV),ZFV!!OneIdeal(S));
            assert rel_cond subset ZFV;
            pp:=PrimesAbove(rel_cond);
            singular_support:=&cat([P in pp select "1" else "0" : P in ss ]);
            singular_support:=Sprint(StringToInteger(singular_support,2));
            assert (singular_support eq "0") eq (S eq ZFV);
        else
            singular_support:="\\N";
        end if;
        string_I:=Join([label_we,singular_support],":");
        Append(~av_fq_we,string_I);
    end for;
        
    // we print all outputs
    fprintf av_fq_isog_output, "%o\n", av_fq_isog;
    for we_line in av_fq_we do
        fprintf av_fq_we_output, "%o\n", we_line;
    end for;
    printf "%o : done\n",label; 
catch e
    printf "*********************************************\n%o\n%o\n", label,e;
    fprintf issues, "*********************************************\n%o\n%o\n", label,e;
end try;
quit;

