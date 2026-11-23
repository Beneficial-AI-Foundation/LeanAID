A[] ((Step.Closed && (obs >= 7200) && (busy == 0)) imply (!(Pump.Temp && (Pump.y < (dur * 60)))))
A[] ((Step.Closed && (obs >= 1800) && (busy == 0)) imply (!((Pump.Temp && (Pump.y < (dur * 60))) && ((tcls == 4) || (tcls == 5)))))
A[] ((Step.Closed && (obs >= 7500) && (busy == 0)) imply (!(Pump.Temp && (Pump.y < (dur * 60)))))
A[] ((Step.Closed && (obs >= 2100) && (busy == 0)) imply (!((Pump.Temp && (Pump.y < (dur * 60))) && ((tcls == 4) || (tcls == 5)))))
