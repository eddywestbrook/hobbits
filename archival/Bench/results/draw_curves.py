import numpy as np
import matplotlib.pyplot as plt
import matplotlib.mlab as mlab
import matplotlib.ticker as ticker
import matplotlib.text as text



t = []
for l in file('biglinear_O2.csv'):
  t.append(l.split())
m = np.matrix(t[1:])
print m[:,0]
print m[:,1:]

xs = m[:,0]
fhb = m[:,1]
hb = m[:,2]
db = m[:,3]
ln = m[:,4]


fig = plt.figure()
ax = fig.add_subplot(111,aspect=(400./3500))
plt.plot(xs,fhb,'k-',xs,hb,'k--',xs,db,'k:',xs,ln,'k-.')
plt.legend(('Fast HOBbitLib', 'HOBbitLib', 'DeBruijn Indices','Locally Nameless'),'upper left')
plt.xlabel('term size')
plt.ylabel('time in ms')
#plt.title('normalization of a big term')

for o in fig.findobj(text.Text):
      o.set_style('italic')

plt.show()
