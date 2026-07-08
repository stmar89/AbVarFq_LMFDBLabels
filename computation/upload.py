# Attach this to a running copy of Sage with the path to the lmfdb in sys.path (so that from lmfdb import db works)

import re, time
from pathlib import Path
from collections import Counter, defaultdict
from sage.all import ZZ
from sage.databases.cremona import class_to_int
from lmfdb import db
import subprocess

def sort_key(label):
    pieces = re.split(r"\.|_|-", label)
    return tuple(int(c) if c.isdigit() else class_to_int(c) for c in pieces)

def create_upload_files(infolder, parallelopts="-j32 --timeout 60"):
    # We create an update file for av_fq_isog and reload/update files for av_fq_weak_equivalences and av_fq_pol
    polcnts = Counter()
    infolder = Path(infolder)

    updated_isog_cols = "label:zfv_singular_primes:zfv_singular_count:zfv_pic_size:pic_prime_gens:size:weak_equivalence_count:endomorphism_ring_count:group_structure_count:all_unpolarized_product:all_polarized_product:cohen_macaulay_max:principal_polarization_count:principal_polarization_count_weighted".split(":")

    we_folder = infolder / "output_wk"
    we_cols = "label:we_number:pic_size:multiplicator_ring:isog_label:ideal_basis_numerators:ideal_basis_denominator:is_invertible:cohen_macaulay_type:dimensions:minimal_overorders:rational_invariants:higher_invariants:conductor:conductor_is_Sprime:conductor_is_Oprime:conductor_Sindex:conductor_Oindex:conductor_class".split(":")
    labels = set(path.name.replace("_wk.txt", "") for path in we_folder.iterdir())
    label_todo = sorted(labels, key=sort_key)

    sing_folder_isog = infolder / "output_sing_primes" / "av_fq_isog"
    sing_isog_cols = "label:zfv_singular_primes".split(":")
    sing_folder_we = infolder / "output_sing_primes" / "av_fq_we"
    sing_we_cols = "label:singular_support".split(":")
    assert labels == set(path.name for path in sing_folder_isog.iterdir()) == set(path.name for path in sing_folder_we.iterdir())

    pol_folder_isog = infolder / "output_pols" / "av_fq_isog"
    pol_isog_cols = "pic_prime_gens:size".split(":")
    pol_folder_we = infolder / "output_pols" / "av_fq_we"
    pol_we_cols = "label:pic_invs:pic_basis:is_product:product_partition:is_conjugate_stable:generator_over_ZFV:is_Zconductor_sum:is_ZFVconductor_sum".split(":")
    pol_folder_pol = infolder / "output_pols" / "av_fq_pol" # only ordinary and some missing CM types
    pol_pol_cols = "label:isog_label:endomorphism_ring:isom_label:degree:kernel:degree_rr:kernel_rr:degree_rl:kernel_rl:degree_lr:kernel_lr:degree_ll:kernel_ll:aut_group:geom_aut_group:is_jacobian:representative".split(":")
    #assert labels == set(path.name for path in pol_folder_isog.iterdir()) == set(path.name for path in pol_folder_we.iterdir())
    pol_labels = set(path.name for path in pol_folder_pol.iterdir())
    pol_label_todo = sorted(pol_labels, key=sort_key)
    assert pol_labels.issubset(labels)

    data = {tbl: defaultdict(lambda: defaultdict(dict)) for tbl in ["weak_equivalences", "isog", "pol"]}
    for these_labels, folder, fname, tbl, cols, suff in [
            (label_todo, we_folder, "wk", "weak_equivalences", we_cols, "_wk.txt"),
            (label_todo, sing_folder_isog, "sing_isog", "isog", sing_isog_cols, ""),
            (label_todo, sing_folder_we, "sing_we", "weak_equivalences", sing_we_cols, ""),
            (pol_label_todo, pol_folder_isog, "pol_isog", "isog", pol_isog_cols, ""),
            (pol_label_todo, pol_folder_we, "pol_we", "weak_equivalences", pol_we_cols, ""),
            (pol_label_todo, pol_folder_pol, "pol_pol", "pol", pol_pol_cols, ""),
    ]:
        print(f"Reading {fname}, {len(these_labels)} files to load")
        T = db["av_fq_"+tbl]
        assert all(col in T.search_cols for col in cols)
        t0 = time.time()
        for i, label in enumerate(these_labels):
            if i % 1000 == 0:
                print(f"Reading {fname}, {i} {label:20} {time.time()-t0}s           ", end="\r")
            with open(folder / (label + suff)) as F:
                for line in F:
                    pieces = line.strip().split(":")
                    assert len(pieces) == len(cols)
                    D = dict(zip(cols, pieces))
                    assert len(D.get("representative", "")) < 131072 # If a single integer surpasses this size then postgres can't load it so we have to use strings instead.  For now, we don't implement anything complicated, just this assert
                    lab = D["label"] if "label" in cols else label
                    for col in cols:
                        if T.col_type[col].endswith("[]"):
                            D[col] = D[col].replace("[", "{").replace("]", "}")
                    data[tbl][label][lab].update(D)
        print(f"Reading {fname}, done in {time.time()-t0}s                               ")

    # Add in data to isog beyond just size,singular_primes,pic_prime_gens
    print(f"Computing columns, {len(labels)} labels to do")
    t0 = time.time()
    for i, label in enumerate(label_todo):
        ISOG = data["isog"][label][label]
        WE = data["weak_equivalences"][label].values()
        ORDERS = [rec for rec in WE if rec["is_invertible"] == "t"]
        POL = data["pol"][label]
        if i % 1000 == 0:
            print(f"Computing columns, {i} {label:20} {time.time()-t0}s           ", end="\r")

        # Add index, number_of_we to the weak equivalence and isogeny data
        we_cnt = len(WE)
        for D in ORDERS:
            if "-" in D["multiplicator_ring"]:
                D["multiplicator_ring"] = D["multiplicator_ring"].split("-")[1] # Discussing on Zulip now....    
            D["index"] = D["multiplicator_ring"].split(".")[0]
        for D in WE:
            D["number_of_we"] = str(we_cnt)
        ISOG["weak_equivalence_count"] = str(we_cnt)

        # The maximum Cohen-Macaulay type
        cm_max = max(int(rec["cohen_macaulay_type"]) for rec in ORDERS)
        ISOG["cohen_macaulay_max"] = str(cm_max)

        # The number of endomorphism rings
        er_cnt = len([rec for rec in ORDERS])
        ISOG["endomorphism_ring_count"] = str(er_cnt)

        # The number of distinct group structures
        gs_cnt = len(set(rec["rational_invariants"] for rec in WE))
        ISOG["group_structure_count"] = str(gs_cnt)

        # The number of singular primes
        P = ISOG["zfv_singular_primes"]
        if P == "{}":
            pcnt = 0
        else:
            if '"' in P:
                pcnt = P.count('","') + 1
            elif "'" in P:
                pcnt = P.count("','") + 1
            else:
                pcnt = P.count(",") + 1
        ISOG["zfv_singular_count"] = str(pcnt)

        if label in pol_labels:
            # The size of the Picard group of Z[F,V]
            maxind = str(max(int(D["index"]) for D in ORDERS))
            ZFV = [w for w in ORDERS if w["index"] == maxind]
            assert len(ZFV) == 1
            ZFV = ZFV[0]
            ISOG["zfv_pic_size"] = ZFV["pic_size"]
            by_aut = defaultdict(Counter)
            for D in POL.values():
                D["pol_ctr"] = D["label"].split(".")[-1]
                by_aut[D["endomorphism_ring"]][QQ(D["aut_group"].split(".")[0])] += 1

            # Whether all isomorphism classes are a nontrivial product.  In the case so far (commutative endomorphism ring), this doesn't depend on whether you're considering them as polarized or unpolarized abelian varieties.
            pcnt = Counter(rec["is_product"] for rec in ORDERS)
            assert pcnt[r"\N"] == 0
            for col in ["all_unpolarized_product", "all_polarized_product"]:
                ISOG[col] = "t" if pcnt["f"] == 0 else "f"
            ISOG["principal_polarization_count"] = str(len([D for D in POL.values() if D["degree"] == "1"]))
            ISOG["principal_polarization_count_weighted"] = str(sum(
                    sum(cnt_with_aut / aut_size for (aut_size, cnt_with_aut) in by_end.items())
                    for by_end in by_aut.values()))
            for D in WE:
                D["principal_polarization_count_weighted"] = str(
                    sum(cnt_with_aut / aut_size for (aut_size, cnt_with_aut) in by_aut[D["label"]].items()))
        else:
            for col in ["all_unpolarized_product", "all_polarized_product", "zfv_pic_size", "principal_polarization_count", "principal_polarization_count_weighted"]:
                ISOG[col] = r"\N"
    print(f"Computing columns, done in {time.time()-t0}s                                 ")

    compute_diagramx(data, parallelopts)
    #print("Setting diagramx")
    #for label in label_todo:
    #    for wlabel, W in data["weak_equivalences"][label].items():
    #        if W["is_invertible"] == "t":
    #            W["diagramx"] = diagramx[wlabel]

    for tbl, these_labels, cols in [
            ("isog", label_todo, updated_isog_cols),
            ("weak_equivalences", label_todo, db.av_fq_weak_equivalences.search_cols),
            ("pol", pol_label_todo, db.av_fq_pol.search_cols)
    ]:
        print(f"Writing av_fq_{tbl}.txt, {len(these_labels)} to write")
        T = db["av_fq_"+tbl]
        t0 = time.time()
        with open(f"av_fq_{tbl}.txt", "w") as F:
            _ = F.write(":".join(cols) + "\n" + ":".join(T.col_type[col] for col in cols) + "\n\n")
            for i, label in enumerate(these_labels):
                if i % 1000 == 0:
                    print(f"Writing av_fq_{tbl}.txt, {i} {label:20} {time.time()-t0}s           ", end="\r")
                for rec in data[tbl][label].values():
                    line = ":".join(rec.get(col,r"\N") for col in cols) + "\n"
                    _ = F.write(line)
        print(f"Writing av_fq_{tbl}.txt, done in {time.time()-t0}s                          ")

def compute_diagramx(data, parallelopts="-j32 --timeout 60"):
    # Given a folder containing weak equivalence data (in the form read by LoadSchemaWKClasses), uses graphviz to find a layout for the endomorphism rings in each weak equivalence class.
    todofile = Path("/tmp/abvar_diagramx.todo")
    indir = Path("/tmp/abvar_diagramx_in")
    outdir = Path("/tmp/abvar_diagramx_out")
    indir.mkdir(exist_ok=True)
    outdir.mkdir(exist_ok=True)
    todo = []
    t0 = time.time()
    print(f"Computing diagramx; writing {len(data['weak_equivalences'])} graphviz input files")
    for i, (label, D) in enumerate(data["weak_equivalences"].items()):
        if i % 1000 == 0:
            print(f"Graphviz input, {i} {label:20} {time.time()-t0}s                           ", end="\r")
        if (outdir / label).exists(): # diagramx already computed for this isogeny class
            continue
        todo.append(label)
        if (indir / label).exists(): # input file already exists for this isogeny class
            continue
        nodes = []
        edges = []
        ranks = defaultdict(list)
        mlabels = []
        for W in D.values():
            if W["is_invertible"] == "t":
                mring, min_over, pic_size = W["multiplicator_ring"], W["minimal_overorders"], W["pic_size"]
                mlabels.append(mring)
                if len(min_over) == 2: # {}
                    min_over = ""
                else:
                    min_over = '","'.join(min_over[1:-1].split(",")) # outside quotes added below
                N = ZZ(W["index"])
                # We get an approximation to the length of the latex output used (we don't omit .1 when there's only one mring of a given index; it won't matter since in that case horizontal space isn't a big deal; and we omit the number of weak equivalence classes with a given mring)
                if N == 1:
                    factored_index = "1"
                else:
                    factored_index = r"*".join((f"{p}{e}" if e > 1 else f"{p}") for (p, e) in N.factor())
                tex = "[%s]%s" % (factored_index, pic_size)
                nodes.append(f'"{mring}" [label="{tex}",shape=plaintext]')
                if min_over:
                    edges.append(f'"{mring}" -> {{"{min_over}"}} [dir=none]')
                ranks[sum(e for (p,e) in N.factor())].append(mring)
        if len(nodes) <= 3:
            # early exit, since we don't need to do anything in these cases
            with open(outdir / label, "w") as F:
                _ = F.write("graph 1.0\n")
                for mring in mlabels:
                    _ = F.write(f'node "{mring}" 0.5\n')
            todo.pop() # Remove label from todo list
        else:
            nodes = ";\n".join(nodes)
            edges = ";\n".join(edges)
            if edges:
                edges += ";" # deal with no edges by moving semicolon here.
            ranks = ";\n".join('{rank=same; "%s"}' % ('" "'.join(labs)) for labs in ranks.values())
            graph = f"""strict digraph "{label}" {{
rankdir=TB;
splines=line;
{edges}
{nodes};
{ranks};
}}
"""
            with open(indir / label, "w") as F:
                _ = F.write(graph)
    print(f"Graphviz input, done in {time.time()-t0}s              ")
    if todo:
        with open(todofile, "w") as Ftodo:
            _ = Ftodo.write("\n".join(todo) + "\n")
        print(f"Running parallel dot on {len(todo)} input files...")
        t0 = time.time()
        subprocess.run('parallel %s -a %s "dot -Tplain -o %s/{1} %s/{1}"' % (parallelopts, todofile, outdir, indir), shell=True, check=True)
        print(f"Parallel dot complete in {time.time()-t0}s")
    print(f"Reading graphviz, {len(data['weak_equivalences'])} output files")
    t0 = time.time()
    for i, path in enumerate(outdir.iterdir()):
        label = path.name
        if i % 1000 == 0:
            print(f"Reading graphviz, {i} {label:20} {time.time()-t0}s            ", end="\r")
        with open(outdir / label) as F:
            # When there are long output lines, dot uses a backslash at the end of the line to indicate a line continuation.
            maxx = 0
            minx = 10000
            lines = []
            continuing = False
            for line in F:
                line = line.strip()
                if continuing:
                    lines[-1] += line
                else:
                    lines.append(line)
                continuing = line[-1] == "\\"
                if continuing:
                    lines[-1] = lines[-1][:-1]
            for line in lines:
                if line == "graph 1.0":
                    scale = 1.0
                elif line.startswith("graph"):
                    scale = float(line.split()[2])
                elif line.startswith("node"):
                    pieces = line.split()
                    mring = pieces[1].replace('"', '')
                    diagram_x = int(round(10000 * float(pieces[2]) / scale))
                    Rlabel = f"{label}-{mring}.1"
                    data["weak_equivalences"][label][Rlabel]["diagramx"] = str(diagram_x)
    print(f"Reading graphviz, done in {time.time()-t0}s                     ")
