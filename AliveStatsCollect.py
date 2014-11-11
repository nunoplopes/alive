
import os
import util

root = [
    "MultiSource",
    "SingleSource",
]


def walkdir(dirname):
    firings = 0
    out_file = file("results.txt", 'w');
    for cur, _dirs, files in os.walk(dirname):
#        pref = ''
#        head, tail = os.path.split(cur)

        cur_output = os.path.join(cur, "Output");

        if os.path.exists(cur_output):
            for out, _odirs, ofiles in os.walk(cur_output):
#                print "output directory is ", out
                indiv_sum = 0
                for f in ofiles:
                    if f.split('.')[-1] == "info":
                        print(f);
                        util.run_command("grep \"total rules fired\" " + os.path.join(out, f) + " | cut -d 'i' -f 1 > log.txt ", verbose=False);
                        myfile = file(os.path.join("log.txt"), 'r');
                        str = myfile.read()

                        value = str.split();

                        for val in value:
                            print "Values for ", os.path.join(out, f), "are: ", val
                            firings = firings + int(val);
                            indiv_sum = indiv_sum + int(val);
                print >> out_file, cur, " & ", indiv_sum, " \\\\ \hline"
    print >> out_file, "Total firings &  ", firings, "\\", "\\\\ \\hline"
    print "Total firings = ", firings
                                       
#                 grep "total rules fired" kc.linked.b\|output directory is  MultiSource/Applications/ALAC/decode/Output
# c.info | cut -d 'i' -f 1
                        # read the state file here


print walkdir("MultiSource");
