"""The three fixes as text replacements on iAPS's minified bundles (FreeAPS/Resources/javascript/bundle).
Same logic as fixes.py, written in the bundle's minified names:
  basal-set-temp.js: l = maxSafeBasal, a = rate, n = profile, s = rT, t = reason(), u = rounded rate
  determine-basal.js: f = minAgo
usage: python3 -I fixes_iaps_bundle.py <finding> <bundle dir>"""
import sys, os

FLOOR = ('function(x,m){var k=x<1?(void 0!==m&&"string"==typeof m.model&&(m.model.endsWith("54")||'
         'm.model.endsWith("23"))?40:20):x<10?20:10;return Math.floor(x*k+1e-9)/k}')
FIXES = {
 'F-04': [('basal-set-temp.js', 'var u=r(760)(a,n);',
           'var u=r(760)(a,n);u>l&&(u=(' + FLOOR + ')(l,n));')],
 'F-11': [('determine-basal.js', '||f>12)return', '||!(f<=12))return')],
 'F-12': [('basal-set-temp.js', 'var l=i.getMaxSafeBasal(n);',
           'var l=i.getMaxSafeBasal(n);if(!("number"==typeof l&&isFinite(l)&&l>0)){var cb=n.current_basal;'
           'if(t(s,"Error: maxSafeBasal "+l+" is not a positive number; check max_basal, max_daily_basal and current_basal"),'
           '!("number"==typeof cb&&isFinite(cb)&&cb>0))return t(s,"canceling temp"),s.duration=0,s.rate=0,s;l=cb}')],
}

finding, d = sys.argv[1], sys.argv[2]
for rel, old, new in FIXES[finding]:
    p = os.path.join(d, rel)
    s = open(p).read()
    if s.count(old) != 1:
        sys.exit('%s: expected 1 match of %r in %s, found %d' % (finding, old, rel, s.count(old)))
    open(p, 'w').write(s.replace(old, new))
    print(p)
