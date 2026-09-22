"""Draw the proved chord minorant; no sampled curve is used as evidence."""
from pathlib import Path
from math import log, exp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent
T = [0, 1, 3, 6, 10, 15, 21]
E = [0, 1, 3, 4, 8, 9, 11]

def minimum(b, mu):
    left, right = 0.01, 0.99
    for _ in range(70):
        x = (left + right) / 2
        z = sum(x ** j for j in b)
        mean = sum(j * x ** j for j in b) / z
        if mean < mu:
            left = x
        else:
            right = x
    x = (left + right) / 2
    return log(sum(x ** j for j in b)) - mu * log(x)

def delta(q, d):
    return minimum(T[:q], 2*d) - minimum(E[:q], d)

left, right = 0.371979, 0.371980
for _ in range(55):
    a = (left + right) / 2
    if delta(6, a) < delta(7, 2*a):
        left = a
    else:
        right = a
a = (left + right) / 2
baseline = delta(6, a)

plt.rcParams.update({'font.family': 'DejaVu Serif', 'font.size': 16,
                     'mathtext.fontset': 'dejavuserif', 'pdf.fonttype': 42,
                     'svg.fonttype': 'none'})
fig, ax = plt.subplots(figsize=(9.0, 3.2))
xs = [float(a), .42, .55, .68, float(2*a)]
ys = [float(baseline), .2703, .2703, .2703, float(baseline)]
blue, red = '#204a70', '#873b40'
for i in range(4):
    ax.plot(xs[i:i+2], ys[i:i+2], color=blue if i<2 else red,
            linestyle='-' if i<2 else (0,(6,3)), linewidth=2.5, zorder=3)
ax.plot(xs, ys, 'o', color='#303030', markersize=4.5, zorder=4)
ax.hlines(float(baseline), xs[0], xs[-1], colors='#505050', linewidth=1.0)
for x, y in zip(xs[1:-1], ys[1:-1]):
    ax.vlines(x, float(baseline), y, colors='#bbbbbb', linewidth=.8, zorder=1)
ax.fill_between(xs, [float(baseline)]*5, ys, color='#e9eef1', zorder=0)
labels = [r'$Q=6$'+'\n'+r'$s=s_6^*$', r'$Q=6$'+'\n'+r'$s=2/5$',
          r'$Q=7$'+'\n'+r'$s=12/25$', r'$Q=7$'+'\n'+r'$s=s_7^*$']
for i, label in enumerate(labels):
    x = (xs[i]+xs[i+1])/2
    y = .27051
    ax.text(x, y, label, ha='center', va='center', fontsize=15,
            color=blue if i<2 else red,
            bbox={'facecolor':'white','edgecolor':'none','pad':1.4,'alpha':.95})
ax.set_xticks(xs, [r'$a_*$', r'$21/50$', r'$11/20$', r'$17/25$', r'$2a_*$'])
ax.set_yticks([float(baseline), .2703], [r'$\log C_*$', r'$0.2703$'])
ax.set_xlim(xs[0]-.01, xs[-1]+.01)
ax.set_ylim(float(baseline)-.00010, .27075)
ax.set_xlabel(r'$\delta=P/n$', labelpad=8)
ax.spines[['top','right']].set_visible(False)
ax.spines[['left','bottom']].set_color('#909090')
ax.tick_params(axis='both', length=4, color='#777777')
fig.tight_layout()
fig.savefig(OUT/'hoffman-certified-cover.pdf')
fig.savefig(OUT/'hoffman-certified-cover.svg')
fig.savefig(OUT/'hoffman-certified-cover.png', dpi=180)
print('Plot coordinates only: a_* =', format(a,'.14g'))
print('Plot coordinates only: C_* =', format(exp(baseline),'.14g'))
print('The four segments depict analytical lower bounds proved in the manuscript.')
