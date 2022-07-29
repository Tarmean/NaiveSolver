import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import seaborn as sns
import os

smartLoop = [(False,12),(True,13),(True,14),(True,16),(False,16),(True,19),(True,20),(False,20),(True,25),(False,21),(False,15),(True,27),(True,51)]
# quickCheck = [(False,1),(False,1),(True,2),(False,2),(False,1),(True,3),(False,2),(False,3),(False,1),(True,4),(False,6),(False,1),(True,7),(False,13),(False,1),(True,14),(False,13),(False,3),(True,16),(False,16),(False,13),(False,6),(True,19),(False,19),(False,13),(False,12),(True,25),(True,50)]
example_data = [{'success': a, 'tree size': b, 'attempt': i} for i, (a, b) in enumerate(reversed(smartLoop))]


frame = pd.DataFrame(example_data, columns=['attempt','success','tree size'])
g = sns.lmplot(y='tree size', x='attempt', data=frame, hue='success', fit_reg=False)
plt.savefig('smartLoop.png')
