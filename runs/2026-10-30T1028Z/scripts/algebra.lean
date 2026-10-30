/-- Degree-4 truncation of `1/A`. -/
noncomputable def B4 (q j s l k x : ℝ) : ℝ :=
  j*x^4/3 + j*x^3/6 + q^2*x^4/4 + 3*q*x^4/2 + q*x^3 + q*x^2/2 - s*x^4/24 + x^4 + x^3 + x^2 + x + 1

/-- `A B4 = 1 + x⁵ C5`. -/
noncomputable def C5 (q j s l k x : ℝ) : ℝ :=
  -j^2*x^2/18 - j^2*x/36 - j*l*x^4/360 - j*l*x^3/720 - j*q^2*x^2/24 - j*q*x^2/4 - j*q*x/3 - j*q/6 + j*s*x^3/72 + j*s*x^2/72 - j*x^2/6 - j*x/6 - j/2 - l*q^2*x^4/480 - l*q*x^4/80 - l*q*x^3/120 - l*q*x^2/240 + l*s*x^4/2880 - l*x^4/120 - l*x^3/120 - l*x^2/120 - l*x/120 - l/120 - q^3*x/8 + q^2*s*x^3/96 - 3*q^2*x/4 - 3*q^2/4 + q*s*x^3/16 + q*s*x^2/24 + q*s*x/24 - q*x/2 - 2*q - s^2*x^3/576 + s*x^3/24 + s*x^2/24 + s*x/24 + s/12 - 1

/-- `∫₀ˣ B4`: `a₀ H₀ χ` to fifth order. -/
noncomputable def P5 (q j s l k x : ℝ) : ℝ :=
  j*x^5/15 + j*x^4/24 + q^2*x^5/20 + 3*q*x^5/10 + q*x^4/4 + q*x^3/6 - s*x^5/120 + x^5/5 + x^4/4 + x^3/3 + x^2/2 + x

/-- `P5 = x P5q`. -/
noncomputable def P5q (q j s l k x : ℝ) : ℝ :=
  j*x^4/15 + j*x^3/24 + q^2*x^4/20 + 3*q*x^4/10 + q*x^3/4 + q*x^2/6 - s*x^4/120 + x^4/5 + x^3/4 + x^2/3 + x/2 + 1

/-- Degree-5 truncation of `P5^2`. -/
noncomputable def M2 (q j s l k x : ℝ) : ℝ :=
  j*x^5/12 + 2*q*x^5/3 + q*x^4/3 + 5*x^5/6 + 11*x^4/12 + x^3 + x^2

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WM2 (q j s l k x : ℝ) : ℝ :=
  j^2*x^4/225 + j^2*x^3/180 + j^2*x^2/576 + j*q^2*x^4/150 + j*q^2*x^3/240 + j*q*x^4/25 + 7*j*q*x^3/120 + 31*j*q*x^2/720 + j*q*x/72 - j*s*x^4/900 - j*s*x^3/1440 + 2*j*x^4/75 + j*x^3/20 + 47*j*x^2/720 + 17*j*x/180 + 7*j/40 + q^4*x^4/400 + 3*q^3*x^4/100 + q^3*x^3/40 + q^3*x^2/60 - q^2*s*x^4/1200 + 11*q^2*x^4/100 + 7*q^2*x^3/40 + 47*q^2*x^2/240 + 2*q^2*x/15 + 23*q^2/180 - q*s*x^4/200 - q*s*x^3/240 - q*s*x^2/360 + 3*q*x^4/25 + q*x^3/4 + 47*q*x^2/120 + 11*q*x/20 + 173*q/180 + s^2*x^4/14400 - s*x^4/300 - s*x^3/240 - s*x^2/180 - s*x/120 - s/60 + x^4/25 + x^3/10 + 47*x^2/240 + 11*x/30 + 137/180

/-- Degree-5 truncation of `P5^3`. -/
noncomputable def M3 (q j s l k x : ℝ) : ℝ :=
  q*x^5/2 + 7*x^5/4 + 3*x^4/2 + x^3

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WM3 (q j s l k x : ℝ) : ℝ :=
  j^2*x^4/180 + j^2*x^3/288 + j*q^2*x^4/240 + 5*j*q*x^4/72 + 17*j*q*x^3/240 + j*q*x^2/36 - j*s*x^4/1440 + 13*j*x^4/180 + 7*j*x^3/60 + 191*j*x^2/1440 + 3*j*x/20 + j/8 + q^3*x^4/30 + q^3*x^3/60 + 29*q^2*x^4/120 + 5*q^2*x^3/16 + 11*q^2*x^2/45 + 19*q^2*x/180 - q*s*x^4/180 - q*s*x^3/360 + 23*q*x^4/60 + 43*q*x^3/60 + 701*q*x^2/720 + 413*q*x/360 + 5*q/4 - s*x^4/144 - 11*s*x^3/1440 - s*x^2/120 - s*x/120 + x^4/6 + 47*x^3/120 + 509*x^2/720 + 211*x/180 + 15/8

/-- Degree-5 truncation of `P5^4`. -/
noncomputable def M4 (q j s l k x : ℝ) : ℝ :=
  2*x^5 + x^4

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WM4 (q j s l k x : ℝ) : ℝ :=
  j*q*x^4/30 + j*q*x^3/48 + 7*j*x^4/60 + 83*j*x^3/480 + 31*j*x^2/240 + j*x/24 + q^3*x^4/40 + 19*q^2*x^4/80 + q^2*x^3/5 + 2*q^2*x^2/15 - q*s*x^4/240 + 5*q*x^4/8 + 81*q*x^3/80 + 17*q*x^2/15 + 3*q*x/4 + 2*q/3 - 7*s*x^4/480 - s*x^3/80 - s*x^2/120 + 7*x^4/20 + 59*x^3/80 + 139*x^2/120 + 13*x/8 + 17/6

/-- Degree-5 truncation of `P5^5`. -/
noncomputable def M5 (q j s l k x : ℝ) : ℝ :=
  x^5

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WM5 (q j s l k x : ℝ) : ℝ :=
  2*j*x^4/15 + 3*j*x^3/20 + j*x^2/24 + q^2*x^4/10 + q^2*x^3/20 + 3*q*x^4/5 + 4*q*x^3/5 + 7*q*x^2/12 + q*x/6 - s*x^4/60 - s*x^3/120 + 2*x^4/5 + 7*x^3/10 + 11*x^2/12 + 4*x/3 + 5/2

/-- Degree-5 truncation of `(1 − A)^2`. -/
noncomputable def N2 (q j s l k x : ℝ) : ℝ :=
  j*q*x^5/6 + j*x^4/3 + q^2*x^4/4 + q*x^3 - s*x^5/12 + x^2

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WN2 (q j s l k x : ℝ) : ℝ :=
  j^2/36 + j*l*x^2/360 - j*s*x/72 + l^2*x^4/14400 + l*q*x/120 - l*s*x^3/1440 + l/60 - q*s/24 + s^2*x^2/576

/-- Degree-5 truncation of `(1 − A)^3`. -/
noncomputable def N3 (q j s l k x : ℝ) : ℝ :=
  j*x^5/2 + 3*q^2*x^5/4 + 3*q*x^4/2 + x^3

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WN3 (q j s l k x : ℝ) : ℝ :=
  j^2*q*x^2/36 + j^2*x/18 + j*l*q*x^4/720 + j*l*x^3/360 + j*q^2*x/8 - j*q*s*x^3/144 + j*q/2 - j*s*x^2/36 + l*q^2*x^3/480 + l*q*x^2/120 - l*s*x^4/1440 + l*x/120 + q^3/8 - q^2*s*x^2/96 - q*s*x/12 + s^2*x^3/288 - s/8

/-- Degree-5 truncation of `(1 − A)^4`. -/
noncomputable def N4 (q j s l k x : ℝ) : ℝ :=
  2*q*x^5 + x^4

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WN4 (q j s l k x : ℝ) : ℝ :=
  j^2*x^2/12 + j*l*x^4/240 + j*q^2*x^2/8 + j*q*x/2 - j*s*x^3/48 + 2*j/3 + l*q^2*x^4/160 + l*q*x^3/80 + l*x^2/120 + 3*q^3*x/8 - q^2*s*x^3/32 + 3*q^2/2 - q*s*x^2/16 - s*x/24

/-- Degree-5 truncation of `(1 − A)^5`. -/
noncomputable def N5 (q j s l k x : ℝ) : ℝ :=
  x^5

/-- Product remainder (`… = … + x⁶ ·`). -/
noncomputable def WN5 (q j s l k x : ℝ) : ℝ :=
  j*q*x^2/3 + j*x/6 + l*q*x^4/60 + l*x^3/120 + q^2*x - q*s*x^3/12 + 5*q/2 - s*x^2/24

/-- `A · Spoly = Fpoly + x⁶ Wf`. -/
noncomputable def Wf (q j s l k x : ℝ) : ℝ :=
  -7*j^2*x^2/80 - 5*j^2*x/144 - j*k^2*x^2/720 + j*k*q*x^2/36 + 17*j*k*x^2/144 + 5*j*k*x/72 + j*k/36 - 7*j*l*x^4/1600 - j*l*x^3/576 - 23*j*q^2*x^2/360 - 173*j*q*x^2/360 - 389*j*q*x/720 - 31*j*q/144 + 7*j*s*x^3/320 + 49*j*s*x^2/2880 - 137*j*x^2/360 - 25*j*x/72 - 299*j/360 - k^2*l*x^4/14400 - k^2*q*x/240 + k^2*s*x^3/2880 - k^2/120 + k*l*q*x^4/720 + 17*k*l*x^4/2880 + k*l*x^3/288 + k*l*x^2/720 + k*q^2*x/12 - k*q*s*x^3/144 + 17*k*q*x/48 + 3*k*q/8 - 17*k*s*x^3/576 - 5*k*s*x^2/288 - k*s*x/144 + 17*k/24 - 23*l*q^2*x^4/7200 - 173*l*q*x^4/7200 - l*q*x^3/72 - l*q*x^2/180 + l*s*x^4/2400 - 137*l*x^4/7200 - 5*l*x^3/288 - 11*l*x^2/720 - l*x/80 - l/120 - 23*q^3*x/120 + 23*q^2*s*x^3/1440 - 173*q^2*x/120 - 73*q^2/60 + 173*q*s*x^3/1440 + 5*q*s*x^2/72 + 19*q*s*x/360 - 137*q*x/120 - 157*q/40 - s^2*x^3/480 + 137*s*x^3/1440 + 25*s*x^2/288 + 11*s*x/144 + 9*s/80 - 137/60
