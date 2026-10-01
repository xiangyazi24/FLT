# Read-only assessment of the restored N18 add_congr gap

Source: 29e80dbc17c5fdf3a194618d65dc0676199e19f5, N18AddCongr.lean (blob 10160a9e6935b4ad56fc36b224db301ff7dce839). This is not an implementation claim or assumption that the lane is unowned.

The corrected target retains the zero-error disjunction. For the integral model a1=1,a2=-1,a3=1,a4=-5,a6=5, source val_coords proves v(x)=-2k and v(y)=-3k for k=v(-x/y)>0 at each finite formal-kernel point.

The inverse-pair branch can be settled directly without the missing N18AddCongrProof file. For Q=-P and P=(x,y), put d=y+x+1. The opposite ordinate is -d, so z(P)=-x/y and z(-P)=x/d. The exact identity is

    z(P)+z(-P) = -x*(x+1)/(y*d).

Since v(x)<0, one has x+1≠0 and v(x+1)=v(x)=-2k. Since v(y)=-3k<-2k=v(x+1), one has d≠0 and v(d)=v(y)=-3k. Therefore both formal parameters have valuation k, and the nonzero addition error for P+(-P)=O has valuation

    2*v(x)-2*v(y)=2*k=v(z(P))+v(z(-P)).

The origin cases are already proved in the source. The remaining serious work is the distinct-x and tangent branches, or a uniformly integral chart identity covering both. It must show the error is zero or has the stated lower bound; using ordPi_add_ge at a possibly zero intermediate sum without the source's nonzero side conditions would be invalid.

Direct fetch of the comment-referenced FLT/Assumptions/MazurProof/N18AddCongrProof.lean at this pin returned HTTP404/NOT_FOUND. No properties of its alleged G_line, BC_factor, or identity8 are assumed here. Ownership and newer source are requested through COMMS before implementation.
