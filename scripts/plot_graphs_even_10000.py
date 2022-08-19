import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
import os



quickCheckList = []

smartCheckList = []


full_block = [(False, 500), (False, 500), (False, 750), (False, 750), (False, 750), (False, 750), (False, 875), (False, 875), (False, 875), (False, 875), (False, 875), (False, 875), (False, 875), (False, 875), (False, 937), (True, 938), (False, 875), (True, 876), (True, 813), (True, 750), (False, 687), (True, 688), (False, 625), (True, 626), (True, 563), (True, 500), (False, 468), (True, 469), (True, 437), (True, 405), (False, 373), (False, 374), (False, 374), (True, 374), (True, 343), (False, 312), (True, 312), (True, 281), (False, 265), (True, 265), (True, 249), (True, 233), (True, 217), (False, 201), (True, 202), (True, 186), (True, 170), (False, 154), (True, 155), (True, 139), (False, 131), (True, 131), (True, 123), (True, 115), (True, 107), (False, 99), (True, 100), (False, 92), (True, 93), (False, 85), (True, 86), (True, 78), (True, 70), (False, 66), (True, 66), (False, 62), (True, 62), (True, 58), (False, 54), (True, 54), (False, 50), (True, 50), (True, 46), (True, 42), (False, 38), (True, 39), (True, 35), (True, 33), (True, 31), (True, 29), (True, 27), (True, 25), (True, 23), (True, 21), (True, 19), (True, 17), (False, 16), (True, 16), (True, 15), (True, 14), (True, 13), (True, 12), (True, 11), (True, 10), (False, 9), (True, 9)]
full_block.reverse()

jump2 = [(True, 9960), (True, 9880), (True, 9760), (True, 9520), (False, 9040), (False, 9020), (True, 9020), (False, 8020), (False, 8520), (False, 8520), (False, 8420), (True, 8420), (True, 7739), (False, 6539), (False, 7139), (True, 7139), (True, 6839), (False, 6689), (True, 6689), (False, 6614), (True, 6614), (True, 6576), (False, 6557), (True, 6558), (False, 6548), (True, 6549), (False, 6544), (True, 6544), (False, 6541), (True, 6542), (True, 6540), (True, 5671), (False, 3933), (False, 4802), (False, 4802), (True, 4706), (False, 4271), (True, 4272), (True, 4054), (True, 3945), (False, 3891), (True, 3891), (True, 3864), (True, 3850), (False, 3843), (True, 3844), (True, 3840), (True, 3838), (False, 3403), (True, 3404), (False, 3186), (True, 3187), (False, 3078), (True, 3078), (True, 3023), (False, 2996), (True, 2996), (False, 2982), (True, 2983), (True, 2976), (False, 2972), (True, 2973), (True, 2971), (True, 2970), (False, 2670), (True, 2670), (False, 2520), (True, 2520), (True, 2445), (True, 2407), (False, 2388), (True, 2389), (False, 2379), (True, 2380), (True, 2375), (True, 2372), (True, 2371), (False, 2121), (True, 2121), (False, 1996), (True, 1996), (True, 1933), (True, 1902), (False, 1886), (True, 1887), (True, 1879), (True, 1875), (True, 1873), (True, 1872), (False, 1622), (True, 1622), (False, 1497), (True, 1497), (True, 1434), (True, 1403), (False, 1387), (True, 1388), (True, 1380), (False, 1376), (True, 1376), (True, 1374), (True, 1373), (False, 1123), (True, 1123), (False, 998), (True, 998), (False, 935), (True, 936), (False, 904), (True, 905), (True, 889), (True, 881), (False, 877), (True, 877), (True, 875), (True, 874), (True, 634), (False, 514), (True, 514), (False, 454), (True, 454), (False, 424), (True, 424), (True, 409), (True, 401), (False, 397), (True, 398), (True, 396), (True, 395), (False, 8), (False, 201), (False, 202), (False, 298), (True, 298), (False, 249), (True, 250), (False, 225), (True, 226), (True, 213), (False, 207), (True, 207), (False, 204), (True, 204), (True, 202), (True, 105), (True, 57), (True, 33), (True, 21), (True, 15), (True, 12), (True, 10)]
jump2.reverse()
crit = [(False, 5000), (False, 5000), (False, 7500), (False, 7500), (False, 8750), (False, 8750), (False, 9375), (False, 9375), (False, 9688), (True, 9687), (False, 9531), (True, 9531), (False, 9453), (True, 9453), (False, 9414), (True, 9414), (False, 9395), (True, 9394), (False, 9385), (True, 9384), (False, 9380), (True, 9379), (False, 9378), (True, 9378), (True, 9377), (True, 9376), (False, 6081), (False, 7671), (False, 6450), (False, 9007), (False, 6469), (True, 9357), (False, 7904), (False, 7903), (True, 8631), (False, 8268), (True, 8267), (False, 8086), (True, 8085), (False, 7995), (True, 7994), (True, 7949), (True, 7927), (True, 7916), (False, 7910), (True, 7910), (True, 7907), (False, 7906), (True, 7906), (True, 7905), (False, 6655), (False, 6655), (False, 7280), (True, 7280), (True, 6968), (True, 6812), (False, 6734), (True, 6733), (True, 6694), (True, 6675), (False, 6665), (True, 6665), (False, 6660), (True, 6660), (False, 6658), (True, 6657), (False, 6656), (True, 6656), (False, 5804), (False, 5803), (True, 6230), (True, 6017), (False, 5910), (True, 5910), (True, 5857), (True, 5830), (False, 5817), (True, 5816), (True, 5810), (True, 5807), (False, 5805), (True, 5805), (False, 5804), (True, 5804), (True, 5179), (True, 4867), (True, 4711), (True, 4633), (False, 4594), (True, 4593), (True, 4574), (True, 4564), (False, 4559), (True, 4559), (True, 4557), (False, 4556), (True, 4556), (True, 4555), (True, 3828), (True, 3465), (False, 3283), (True, 3283), (True, 3192), (True, 3147), (True, 3124), (True, 3113), (False, 3107), (True, 3107), (False, 3104), (True, 3104), (False, 3103), (True, 3103), (True, 3102), (False, 2022), (True, 2932), (False, 2392), (True, 2392), (True, 2122), (True, 1987), (True, 1920), (False, 1886), (True, 1886), (True, 1869), (True, 1861), (False, 1857), (True, 1856), (False, 1854), (True, 1854), (False, 1853), (True, 1853), (True, 1541), (False, 1385), (True, 1384), (True, 1306), (True, 1267), (False, 1248), (True, 1247), (True, 1238), (True, 1233), (False, 1231), (True, 1230), (False, 1229), (True, 1229), (True, 1045), (True, 953), (False, 907), (True, 906), (False, 883), (True, 883), (True, 872), (True, 866), (False, 863), (True, 863), (False, 862), (True, 862), (True, 861), (False, 188), (True, 682), (False, 346), (True, 345), (False, 177), (True, 177), (False, 93), (True, 93), (True, 51), (False, 30), (True, 30), (False, 20), (True, 19), (False, 14), (True, 14), (False, 12), (True, 11), (False, 10), (True, 10)]
crit.reverse()

quickXPlain = []
quickXPlain.reverse()

quickXPlainBase = []
quickXPlainBase.reverse()

deltaDebug = []
deltaDebug.reverse()
# example_data = {}
# for k,v in {'smartLoop':smartLoop,'smartCheck':smartCheck}.items():
#     example_data = [{'OracleResult': a, 'tree size': b, 'attempt': i} for i, (a, b) in enumerate(reversed(v))]
#     frame = pd.DataFrame(example_data, columns=['attempt','OracleResult','tree size'])

#     sns.lineplot(x='attempt', y='tree size', data=frame, label=k)


example_data = []
print("even 10000")
for k,v in {'QuickCheck':quickCheckList,'QuickCheck with Permutations':smartCheckList, 'Half Blocking': full_block, 'Crit Blocking': crit, 'Adaptive Delete Blocking': jump2, 'QuickXPlain Fixed': quickXPlain, 'QuickXPlain Paper': quickXPlainBase, 'Delta Debugging': deltaDebug}.items():
    length = len(v)
    total = sum(a[1] for a in v)
    if length > 0:
         print("|", k, "|", length, "|", total, "|")
    example_data.extend({'OracleResult': a, 'size': b, 'attempt': i, 'algorithm': k} for i, (a, b) in enumerate(reversed(v)))
frame = pd.DataFrame(example_data, columns=['attempt','OracleResult','size', 'algorithm'])
g = sns.lmplot(x='attempt', y='size', col='algorithm', hue='OracleResult', data=frame, palette='muted', fit_reg=False, col_wrap=2)
plt.savefig('scatters_even_10000.png')
# sns.lmplot(y='tree size', x='attempt', data=frame, hue='OracleResult', fit_reg=False)

