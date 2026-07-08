##################
# Folders
##################

TODO update next
fld_comp = /data/stmar/287_abvarfq_lmfdb_recomputation/
# where all the scripts are
fld_scripts = ~/AbVarFq_LMFDBLabels/computation/

##################
# inputs
##################

input = ${fld_scripts}weil_poly_sqfree_ord_cs.txt

##################
# my log and issue files
##################

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

TODO
degree_bounds = [4,9,25]
# 20250711 we are only doing principal polarizations, until the faster code is ready
# see Todo file


##################
# scripts for logging
##################

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

##################
# script
##################
