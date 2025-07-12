##################
# Folders
##################

fld_comp = ~/287_abvarfq_lmfdb_recomputation/
# where all the scripts are
fld_scripts = ~/AbVarFq_LMFDBLabels/computation/

##################
# inputs
##################

# coeffs of the input poly, sorted (see above)
# after some thinking I have decided to remove 3.25 from the first round of recomputation
#input = ${fld_scripts}weil_poly_sqfree_ord_cs.txt
#input_ord = ${fld_scripts}weil_poly_sqfree_ord.txt
input = ${fld_scripts}weil_poly_sqfree_ord_cs_no_3_25.txt
input_ord = ${fld_scripts}weil_poly_sqfree_ord_no_3_25.txt
# where to store versions used and status (see below)

# for script_pols
input_cm_missing = ${fld_scripts}input_cm_missing

# for script_pols
input_fast_1 = ${fld_scripts}input_fast_1
input_fast_2 = ${fld_scripts}input_fast_2
input_fast_3 = ${fld_scripts}input_fast_3
input_fast_4 = ${fld_scripts}input_fast_4

input_slow_1 = ${fld_scripts}input_slow_1
input_slow_2 = ${fld_scripts}input_slow_2
input_slow_3 = ${fld_scripts}input_slow_3
input_slow_4 = ${fld_scripts}input_slow_4
# for tests
input_test_pol = ${fld_scripts}input_test_pol

##################
# my log and issue files
##################

my_log = ${fld_comp}my_log
# we collect here the issue from the scripts
issues_wk = ${fld_comp}issues_wk
issues_cm = ${fld_comp}issues_cm
issues_pols = ${fld_comp}issues_pols
issues_sing_primes = ${fld_comp}issues_sing_primes

##################
# output folders
##################

fld_out_wk = ${fld_comp}output_wk/
fld_out_cm = ${fld_comp}output_cm/
fld_out_pols = ${fld_comp}output_pols/
fld_out_sing_primes = ${fld_comp}output_sing_primes/

##################
# degrees of non-princ. 
# pols to be computed
##################

degree_bounds = [4,9,25]
# 20250711 we are only doing principal polarizations, until the faster code is ready
# see Todo file


##################
# scripts for logging
##################

rm_log:
	rm ${my_log} || true

log_versions_last_commits:
	@date >> ${my_log}
	@echo "magma version:" >> ${my_log}
	@magma -b -e 'GetVersion();' >> ${my_log}
	@echo last git commit for CHIMP: >> ${my_log}
	@git -C ~/CHIMP/ log -n 1 --pretty=format:"%H" >> ${my_log}
	@echo "\nlast git commit for AlgEt:" >> ${my_log}
	@git -C ~/AlgEt/ log -n 1 --pretty=format:"%H" >> ${my_log}
	@echo "\nlast git commit for AbVarFq_LMFDBLabels:" >> ${my_log}
	@git -C ~/AbVarFq_LMFDBLabels/ log -n 1 --pretty=format:"%H" >> ${my_log}
	@echo "\n" >> ${my_log}

echo_status:
	@echo "status on:"
	@date
	@echo "number of inputs :"
	@cat ${input} | wc -l
	@echo "number of ordinary inputs :"
	@cat ${input_ord} | wc -l
	@echo "script_wk completed :"
	@ls ${fld_out_wk} | wc -l
	@echo "script_cm completed:"
	@ls ${fld_out_cm} | wc -l
	@echo "script_pols completed :"
	@ls ${fld_out_pols}av_fq_isog | wc -l
	@echo "script_sing_primes completed :"
	@ls ${fld_out_sing_primes}av_fq_isog | wc -l

log_status:
	@echo "status on:" >> ${my_log}
	@date >> ${my_log}
	@echo "number of inputs :" >> ${my_log}
	@cat ${input} | wc -l >> ${my_log}
	@echo "number of ordinary inputs :" >> ${my_log}
	@cat ${input_ord} | wc -l >> ${my_log}
	@echo "script_wk completed :" >> ${my_log}
	@ls ${fld_out_wk} | wc -l >> ${my_log}
	@echo "script_cm completed:" >> ${my_log}
	@ls ${fld_out_cm} | wc -l >> ${my_log}
	@echo "script_pols completed :" >> ${my_log}
	@ls ${fld_out_pols}av_fq_isog | wc -l >> ${my_log}
	@echo "script_sing_primes completed :" >> ${my_log}
	@ls ${fld_out_sing_primes}av_fq_isog | wc -l >> ${my_log}
	@echo "\n" >> ${my_log}

status:
	@make -s echo_status
	@make -s log_status

##################
# scripts for weak eq classes
##################

run_script_wk:
	@echo "(re)starting run_script_wk on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel -j 20 --resume --joblog ${fld_comp}joblog_wk -a ${input} magma -b fld_out:=${fld_out_wk} issues:=${issues_wk} s:={} ${fld_scripts}script_wk.m
	@echo "run_script_wk has finished on:" >> ${my_log}
	@date >> ${my_log}

clean_failed_script_wk:
	rm ~/287_abvarfq_lmfdb_recomputation/output_wk/*
	rm ~/287_abvarfq_lmfdb_recomputation/joblog_wk
	rm ~/287_abvarfq_lmfdb_recomputation/issues_wk

run_script_sing_primes:
	@echo "(re)starting run_script_sing_primes on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel -j 20 --u --resume --joblog ${fld_comp}joblog_sing_primes -a ${input} magma -b fld_out_wk:=${fld_out_wk} fld_out_sing_primes:=${fld_out_sing_primes} issues:=${issues_sing_primes} s:={} ${fld_scripts}script_sing_primes.m
	@echo "run_script_sing_primes has finished on:" >> ${my_log}
	@date >> ${my_log}

clean_failed_script_sing_primes:
	rm ${fld_comp}joblog_sing_primes 
	rm ${fld_out_sing_primes}av_fq_isog/* || true
	rm ${fld_out_sing_primes}av_fq_we/* || true

##################
# scripts for cm-types
##################

run_script_cm:
	@echo "(re)starting run_script_cm on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel -j 18 --memsuspend 100G --resume --joblog ${fld_comp}joblog_cm -a ${input_ord} magma -b fld_out:=${fld_out_cm} issues:=${issues_cm} s:={} ${fld_scripts}script_cm.m
	@echo "run_script_cm has finished on:" >> ${my_log}
	@date >> ${my_log}

clean_failed_script_cm:
	rm ~/287_abvarfq_lmfdb_recomputation/output_cm/*
	rm ~/287_abvarfq_lmfdb_recomputation/joblog_cm
	rm ~/287_abvarfq_lmfdb_recomputation/issues_cm

jobs_cm = 18
run_script_cm_missing:
	@echo "(re)starting run_script_cm_missing on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel -j ${jobs_cm} --u --resume --joblog ${fld_comp}joblog_cm_missing -a ${input_cm_missing} magma -b fld_out:=${fld_out_cm} issues:=${issues_cm} s:={} ${fld_scripts}script_cm_missing.m
	@echo "run_script_cm_missing has finished on:" >> ${my_log}
	@date >> ${my_log}

##################
# scripts for polarizations
##################

timeout = 300
run_script_pols_fast1:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel --eta --timeout ${timeout} --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols_fast1 -a ${input_fast_1} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}

run_script_pols_fast2:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel --eta  --timeout ${timeout} --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols_fast2 -a ${input_fast_2} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}


run_script_pols_fast3:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel --eta  --timeout ${timeout} --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols_fast3 -a ${input_fast_3} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}


run_script_pols_fast4:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel --eta  --timeout ${timeout} --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols_fast4 -a ${input_fast_4} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}

run_script_pols_slow1:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel --eta  --timeout ${timeout} --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols_slow1 -a ${input_slow_1} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}


run_script_pols_slow2:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel --eta  --timeout ${timeout} --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols_slow2 -a ${input_slow_2} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}


run_script_pols_slow3:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel --eta  --timeout ${timeout} --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols_slow3 -a ${input_slow_3} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}


run_script_pols_slow4:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel --eta --timeout ${timeout}  --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols_slow4 -a ${input_slow_4} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}

clean_failed_script_pols:
	rm -r ~/287_abvarfq_lmfdb_recomputation/output_pols/ || true
	mkdir -p ~/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_pol
	mkdir -p ~/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_we
	mkdir -p ~/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_isog
	mkdir -p ~/287_abvarfq_lmfdb_recomputation/output_pols/allproduct
	rm ~/287_abvarfq_lmfdb_recomputation/joblog_pols* || true
	rm ~/287_abvarfq_lmfdb_recomputation/issues_pols* || true

##################
# folders and scripts 
# for testing polarisations
##################

fld_out_pols_test1 = ${fld_comp}output_pols_test1/
fld_out_pols_test2 = ${fld_comp}output_pols_test2/
issues_pols_test1 = ${fld_comp}issues_pols_test1
issues_pols_test2 = ${fld_comp}issues_pols_test2

run_script_pols_test:
	@echo "\n########## 1st parallel ##########\n"
	parallel -j 20 --timeout 120 --resume --joblog ${fld_comp}joblog_pols_test1 -a ${input_test_pol} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols_test1} issues:=${issues_pols_test1} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m || true
	@echo "\n########## 2nd parallel ##########\n"
	parallel -j 20 --timeout 120 --resume --joblog ${fld_comp}joblog_pols_test2 -a ${input_test_pol} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols_test2} issues:=${issues_pols_test2} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m || true
	@echo "\n########## magma test script ##########\n"
	magma -b ~/AbVarFq_LMFDBLabels/tests/20250627_test_script_pols.txt

clean_failed_script_pols_test:
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols_test1/av_fq_pol/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols_test1/av_fq_we/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols_test1/av_fq_isog/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols_test1/allproduct/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/joblog_pols_test1 || true
	rm ~/287_abvarfq_lmfdb_recomputation/issues_pols_test1 || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols_test2/av_fq_pol/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols_test2/av_fq_we/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols_test2/av_fq_isog/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols_test2/allproduct/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/joblog_pols_test2 || true
	rm ~/287_abvarfq_lmfdb_recomputation/issues_pols_test2 || true

##################
# folders and scripts for 
# all computations for g=3, q=25
##################

fld_comp_3_25 = ~/287_abvarfq_lmfdb_recomputation_3_25/
fld_out_wk_3_25 = ${fld_comp_3_25}output_wk/
my_log_3_25 = ${fld_comp_3_25}my_log
input_3_25 = ${fld_scripts}weil_poly_sqfree_ord_only_3_25.txt
issues_wk_3_25 = ${fld_comp_3_25}issues_wk_3_25

rm_log_3_25:
	rm ${my_log_3_25} || true

log_versions_last_commits_3_25:
	@date >> ${my_log_3_25}
	@echo "magma version:" >> ${my_log_3_25}
	@magma -b -e 'GetVersion();' >> ${my_log_3_25}
	@echo last git commit for CHIMP: >> ${my_log_3_25}
	@git -C ~/CHIMP/ log -n 1 --pretty=format:"%H" >> ${my_log_3_25}
	@echo "\nlast git commit for AlgEt:" >> ${my_log_3_25}
	@git -C ~/AlgEt/ log -n 1 --pretty=format:"%H" >> ${my_log_3_25}
	@echo "\nlast git commit for AbVarFq_LMFDBLabels:" >> ${my_log_3_25}
	@git -C ~/AbVarFq_LMFDBLabels/ log -n 1 --pretty=format:"%H" >> ${my_log_3_25}
	@echo "\n" >> ${my_log_3_25}

jobs_wk_3_25 = 18
run_script_wk_3_25:
	@echo "(re)starting run_script_wk_3_25 on:" >> ${my_log_3_25}
	@make -s log_versions_last_commits_3_25
	parallel -j ${jobs_wk_3_25} --memsuspend 100G -resume --joblog ${fld_comp_3_25}joblog_wk_3_25 -a ${input_3_25} magma -b fld_out:=${fld_out_wk_3_25} issues:=${issues_wk_3_25} s:={} ${fld_scripts}script_wk.m
	@echo "run_script_wk_3_25 has finished on:" >> ${my_log_3_25}
	@date >> ${my_log_3_25}

clean_failed_script_wk_3_25:
	rm ${fld_out_wk_3_25}* || true
	rm ${fld_comp_3_25}joblog_wk_3_25 || true
	rm ${issues_wk_3_25} || true

# TODO the following are not tested

jobs_sing_primes_3_25 = 18
fld_out_sing_primes_3_25 = ${fld_comp_3_25}output_sing_primes/
issues_sing_primes_3_25 = ${fld_comp_3_25}issues_sing_primes_3_25

run_script_sing_primes_3_25:
	@echo "(re)starting run_script_sing_primes_3_25 on:" >> ${my_log_3_25}
	@make -s log_versions_last_commits_3_25
	parallel -j ${jobs_sing_primes_3_25} --u --resume --joblog ${fld_comp_3_25}joblog_sing_primes_3_25 -a ${input_3_25} magma -b fld_out_wk:=${fld_out_wk_3_25} fld_out_sing_primes:=${fld_out_sing_primes_3_25} issues:=${issues_sing_primes_3_25} s:={} ${fld_scripts}script_sing_primes.m
	@echo "run_script_sing_primes_wk_3_25 has finished on:" >> ${my_log_wk_3_25}
	@date >> ${my_log_wk_3_25}

clean_failed_script_sing_primes_3_25:
	rm ${fld_comp_3_25}joblog_sing_primes_wk_3_25 
	rm ${fld_out_sing_primes_wk_3_25}av_fq_isog/* || true
	rm ${fld_out_sing_primes_wk_3_25}av_fq_we/* || true

fld_out_cm_3_25 = ${fld_comp_3_25}output_cm/
issues_cm_3_25 = ${fld_comp_3_25}issues_cm_3_25

run_script_cm_3_25:
	@echo "(re)starting run_script_cm_3_25 on:" >> ${my_log_3_25}
	@make -s log_versions_last_commits_3_25
	parallel -j 10 --resume --joblog ${fld_comp_3_25}joblog_cm_3_25 -a ${input_3_25} magma -b fld_out:=${fld_out_cm_3_25} issues:=${issues_cm_3_25} s:={} ${fld_scripts}script_cm.m
	@echo "run_script_cm_3_25 has finished on:" >> ${my_log_3_25}
	@date >> ${my_log_3_25}

clean_failed_script_cm_3_25:
	rm ${fld_out_cm_3_25}*
	rm ${fld_comp_3_25}joblog_cm_3_25
	rm ${issues_cm_3_25}

timeout_pols_3_25 = 3600
fld_out_pols_3_25 = ${fld_comp_3_25}output_pols/
issues_pols_3_25 = ${fld_comp_3_25}issues_pols_3_25

run_script_pols_3_25:
	@echo "(re)starting run_script_pols_3_25 on:" >> ${my_log_3_25}
	@make -s log_versions_last_commits_3_25
	parallel --eta --timeout ${timeout_pols_3_25}  --resume --joblog ${fld_comp_3_25}joblog_pols_3_25 -a ${input_3_25} magma -b fld_comp:=${fld_comp_3_25} fld_out_wk:=${fld_out_wk_3_25} fld_out_cm:=${fld_out_cm_3_25} fld_out_pols:=${fld_out_pols_3_25} issues:=${issues_pols_3_25} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols_3_25 has finished on:" >> ${my_log_3_25}for ll in l :
	@date >> ${my_log_3_25}

clean_failed_script_pols_3_25:
	rm -r ${fld_out_pols_3_25} || true
	mkdir -p ${fld_out_pols_3_25}av_fq_pol
	mkdir -p ${fld_out_pols_3_25}av_fq_we
	mkdir -p ${fld_out_pols_3_25}av_fq_isog
	mkdir -p ${fld_out_pols_3_25}allproduct
	rm ${fld_comp_3_25}joblog_pols_3_25 || true
	rm ${issues_pols_3_25} || true

echo_status_3_25:
	@echo "status on_3_25"
	@date
	@echo "number of inputs_3_25:"
	@cat ${input_3_25} | wc -l
	@echo "script_wk_3_25 completed :"
	@ls ${fld_out_wk_3_25} | wc -l
	@echo "script_cm_3_25 completed:"
	@ls ${fld_out_cm_3_25} | wc -l
	@echo "script_pols_3_25 completed :"
	@ls ${fld_out_pols_3_25}av_fq_isog | wc -l
	@echo "script_sing_primes_3_25 completed :"
	@ls ${fld_out_sing_primes_3_25}av_fq_isog | wc -l

log_status_3_25:
	@echo "status on_3_25:" >> ${my_log_3_25}
	@date >> ${my_log_3_25}
	@echo "number of inputs_3_25 :" >> ${my_log_3_25}
	@cat ${input_3_25} | wc -l >> ${my_log_3_25}
	@echo "script_wk_3_25 completed :" >> ${my_log_3_25}
	@ls ${fld_out_wk_3_25} | wc -l >> ${my_log_3_25}
	@echo "script_cm completed:" >> ${my_log_3_25}
	@ls ${fld_out_cm_3_25} | wc -l >> ${my_log_3_25}
	@echo "script_pols completed :" >> ${my_log_3_25}
	@ls ${fld_out_pols_3_25}av_fq_isog | wc -l >> ${my_log_3_25}
	@echo "script_sing_primes completed :" >> ${my_log_3_25}
	@ls ${fld_out_sing_primes_3_25}av_fq_isog | wc -l >> ${my_log_3_25}
	@echo "\n" >> ${my_log_3_25}

status_3_25:
	@make -s echo_status_3_25
	@make -s log_status_3_25

