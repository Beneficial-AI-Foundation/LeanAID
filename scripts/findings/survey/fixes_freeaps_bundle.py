"""The three fixes on FreeAPS X's minified bundles (names in this build: setTempBasal(t,r,o,i,u),
s = maxSafeBasal, l = rounded rate, o = profile, i = rT, a() = reason(); determine-basal v = minAgo).
usage: python3 -I fixes_freeaps_bundle.py <finding> <bundle dir>"""
import sys, os
FLOOR = ('function(x,m){var k=x<1?(void 0!==m&&"string"==typeof m.model&&(m.model.endsWith("54")||'
         'm.model.endsWith("23"))?40:20):x<10?20:10;return Math.floor(x*k+1e-9)/k}')
FIXES = {
 'F-04': [('basal-set-temp.js', 'var l=e(6880)(t,o);', 'var l=e(6880)(t,o);l>s&&(l=(' + FLOOR + ')(s,o));', 1)],
 'F-11': [('determine-basal.js', 'v>12||v<-5', '!(v<=12&&v>=-5)', 2)],
 'F-12': [('basal-set-temp.js', 'var s=n.getMaxSafeBasal(o);',
           'var s=n.getMaxSafeBasal(o);if(!("number"==typeof s&&isFinite(s)&&s>0)){var cb=o.current_basal;'
           'if(a(i,"Error: maxSafeBasal "+s+" is not a positive number; check max_basal, max_daily_basal and current_basal"),'
           '!("number"==typeof cb&&isFinite(cb)&&cb>0))return a(i,"canceling temp"),i.duration=0,i.rate=0,i;s=cb}', 1)],
}
finding, d = sys.argv[1], sys.argv[2]
for rel, old, new, n in FIXES[finding]:
    p = os.path.join(d, rel); s = open(p).read()
    if s.count(old) != n: sys.exit('%s: expected %d matches of %r in %s, found %d' % (finding, n, old, rel, s.count(old)))
    open(p, 'w').write(s.replace(old, new)); print(p)
