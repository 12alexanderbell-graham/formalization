import Checked.Math.GCerts3

/-! Gelfand problem, `GChain`: (generated certificates; promoted verbatim from `Work/Math/GChain.lean`). Promoted from `Work/Math/GChain.lean`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Checked.Math.GCerts
open Set Checked.Sim Checked.Math.LECell Checked.Math.GCell Checked.Math.GHelp

/-- Chaining of the start and all cells. -/
theorem chain {w φ : ℝ → ℝ} (hw : ∀ s ∈ Icc (0 : ℝ) (41 / 10), HasDerivWithinAt w (φ s) (Icc 0 (41 / 10)) s) (hφ0 : ContinuousWithinAt φ (Icc 0 (41 / 10)) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) (41 / 10),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 (41 / 10)) s)
    (h0 : w 0 = 0) :
    (∀ t ∈ Ioc (0 : ℝ) (3 : ℝ), 0 < 2 + t * φ t) ∧ (∀ t ∈ Icc (3 : ℝ) (814299369/200000000 : ℝ), 0 < φ t + t * Real.exp (w t)) ∧
      |Real.exp (w (1017874211/250000000 : ℝ)) - (1001983101246205873/5000000000000000000 : ℝ)| ≤ (31316544345759/10000000000000000000000000 : ℝ) ∧ |φ (1017874211/250000000 : ℝ) - (-3070123956454913517/6250000000000000000 : ℝ)| ≤ (31316544345759/10000000000000000000000000 : ℝ) ∧
      |φ (814299369/200000000 : ℝ) - (-24560991649594292929/50000000000000000000 : ℝ)| ≤ (156582722125403/50000000000000000000000000 : ℝ) := by
  obtain ⟨n0, a0, b0⟩ := startI hw hφ0 hφ h0
  obtain ⟨n1, a1, b1⟩ := step0 hw hφ n0 a0 b0
  obtain ⟨n2, a2, b2⟩ := step1 hw hφ n1 a1 b1
  obtain ⟨n3, a3, b3⟩ := step2 hw hφ n2 a2 b2
  obtain ⟨n4, a4, b4⟩ := step3 hw hφ n3 a3 b3
  obtain ⟨n5, a5, b5⟩ := step4 hw hφ n4 a4 b4
  obtain ⟨n6, a6, b6⟩ := step5 hw hφ n5 a5 b5
  obtain ⟨n7, a7, b7⟩ := step6 hw hφ n6 a6 b6
  obtain ⟨n8, a8, b8⟩ := step7 hw hφ n7 a7 b7
  obtain ⟨n9, a9, b9⟩ := step8 hw hφ n8 a8 b8
  obtain ⟨n10, a10, b10⟩ := step9 hw hφ n9 a9 b9
  obtain ⟨n11, a11, b11⟩ := step10 hw hφ n10 a10 b10
  obtain ⟨n12, a12, b12⟩ := step11 hw hφ n11 a11 b11
  obtain ⟨n13, a13, b13⟩ := step12 hw hφ n12 a12 b12
  obtain ⟨n14, a14, b14⟩ := step13 hw hφ n13 a13 b13
  obtain ⟨n15, a15, b15⟩ := step14 hw hφ n14 a14 b14
  obtain ⟨n16, a16, b16⟩ := step15 hw hφ n15 a15 b15
  obtain ⟨n17, a17, b17⟩ := step16 hw hφ n16 a16 b16
  obtain ⟨n18, a18, b18⟩ := step17 hw hφ n17 a17 b17
  obtain ⟨n19, a19, b19⟩ := step18 hw hφ n18 a18 b18
  obtain ⟨n20, a20, b20⟩ := step19 hw hφ n19 a19 b19
  obtain ⟨n21, a21, b21⟩ := step20 hw hφ n20 a20 b20
  obtain ⟨n22, a22, b22⟩ := step21 hw hφ n21 a21 b21
  obtain ⟨n23, a23, b23⟩ := step22 hw hφ n22 a22 b22
  obtain ⟨n24, a24, b24⟩ := step23 hw hφ n23 a23 b23
  obtain ⟨n25, a25, b25⟩ := step24 hw hφ n24 a24 b24
  obtain ⟨n26, a26, b26⟩ := step25 hw hφ n25 a25 b25
  obtain ⟨n27, a27, b27⟩ := step26 hw hφ n26 a26 b26
  obtain ⟨n28, a28, b28⟩ := step27 hw hφ n27 a27 b27
  obtain ⟨n29, a29, b29⟩ := step28 hw hφ n28 a28 b28
  obtain ⟨n30, a30, b30⟩ := step29 hw hφ n29 a29 b29
  obtain ⟨n31, a31, b31⟩ := step30 hw hφ n30 a30 b30
  obtain ⟨n32, a32, b32⟩ := step31 hw hφ n31 a31 b31
  obtain ⟨n33, a33, b33⟩ := step32 hw hφ n32 a32 b32
  obtain ⟨n34, a34, b34⟩ := step33 hw hφ n33 a33 b33
  obtain ⟨n35, a35, b35⟩ := step34 hw hφ n34 a34 b34
  obtain ⟨n36, a36, b36⟩ := step35 hw hφ n35 a35 b35
  obtain ⟨n37, a37, b37⟩ := step36 hw hφ n36 a36 b36
  obtain ⟨n38, a38, b38⟩ := step37 hw hφ n37 a37 b37
  obtain ⟨n39, a39, b39⟩ := step38 hw hφ n38 a38 b38
  obtain ⟨n40, a40, b40⟩ := step39 hw hφ n39 a39 b39
  obtain ⟨n41, a41, b41⟩ := step40 hw hφ n40 a40 b40
  obtain ⟨n42, a42, b42⟩ := step41 hw hφ n41 a41 b41
  obtain ⟨n43, a43, b43⟩ := step42 hw hφ n42 a42 b42
  obtain ⟨n44, a44, b44⟩ := step43 hw hφ n43 a43 b43
  obtain ⟨n45, a45, b45⟩ := step44 hw hφ n44 a44 b44
  obtain ⟨n46, a46, b46⟩ := step45 hw hφ n45 a45 b45
  obtain ⟨n47, a47, b47⟩ := step46 hw hφ n46 a46 b46
  obtain ⟨n48, a48, b48⟩ := step47 hw hφ n47 a47 b47
  obtain ⟨n49, a49, b49⟩ := step48 hw hφ n48 a48 b48
  obtain ⟨n50, a50, b50⟩ := step49 hw hφ n49 a49 b49
  obtain ⟨n51, a51, b51⟩ := step50 hw hφ n50 a50 b50
  obtain ⟨n52, a52, b52⟩ := step51 hw hφ n51 a51 b51
  obtain ⟨n53, a53, b53⟩ := step52 hw hφ n52 a52 b52
  obtain ⟨n54, a54, b54⟩ := step53 hw hφ n53 a53 b53
  obtain ⟨n55, a55, b55⟩ := step54 hw hφ n54 a54 b54
  obtain ⟨n56, a56, b56⟩ := step55 hw hφ n55 a55 b55
  obtain ⟨n57, a57, b57⟩ := step56 hw hφ n56 a56 b56
  obtain ⟨n58, a58, b58⟩ := step57 hw hφ n57 a57 b57
  obtain ⟨n59, a59, b59⟩ := step58 hw hφ n58 a58 b58
  obtain ⟨n60, a60, b60⟩ := step59 hw hφ n59 a59 b59
  obtain ⟨n61, a61, b61⟩ := step60 hw hφ n60 a60 b60
  obtain ⟨n62, a62, b62⟩ := step61 hw hφ n61 a61 b61
  obtain ⟨n63, a63, b63⟩ := step62 hw hφ n62 a62 b62
  obtain ⟨n64, a64, b64⟩ := step63 hw hφ n63 a63 b63
  obtain ⟨n65, a65, b65⟩ := step64 hw hφ n64 a64 b64
  obtain ⟨n66, a66, b66⟩ := step65 hw hφ n65 a65 b65
  obtain ⟨n67, a67, b67⟩ := step66 hw hφ n66 a66 b66
  obtain ⟨n68, a68, b68⟩ := step67 hw hφ n67 a67 b67
  obtain ⟨n69, a69, b69⟩ := step68 hw hφ n68 a68 b68
  obtain ⟨n70, a70, b70⟩ := step69 hw hφ n69 a69 b69
  obtain ⟨n71, a71, b71⟩ := step70 hw hφ n70 a70 b70
  obtain ⟨n72, a72, b72⟩ := step71 hw hφ n71 a71 b71
  obtain ⟨n73, a73, b73⟩ := step72 hw hφ n72 a72 b72
  obtain ⟨n74, a74, b74⟩ := step73 hw hφ n73 a73 b73
  obtain ⟨n75, a75, b75⟩ := step74 hw hφ n74 a74 b74
  obtain ⟨n76, a76, b76⟩ := step75 hw hφ n75 a75 b75
  obtain ⟨n77, a77, b77⟩ := step76 hw hφ n76 a76 b76
  obtain ⟨n78, a78, b78⟩ := step77 hw hφ n77 a77 b77
  obtain ⟨n79, a79, b79⟩ := step78 hw hφ n78 a78 b78
  obtain ⟨n80, a80, b80⟩ := step79 hw hφ n79 a79 b79
  obtain ⟨n81, a81, b81⟩ := step80 hw hφ a80 b80
  obtain ⟨n82, a82, b82⟩ := step81 hw hφ n81 a81 b81
  obtain ⟨n83, a83, b83⟩ := step82 hw hφ n82 a82 b82
  obtain ⟨n84, a84, b84⟩ := step83 hw hφ n83 a83 b83
  obtain ⟨n85, a85, b85⟩ := step84 hw hφ n84 a84 b84
  obtain ⟨n86, a86, b86⟩ := step85 hw hφ n85 a85 b85
  obtain ⟨n87, a87, b87⟩ := step86 hw hφ n86 a86 b86
  obtain ⟨n88, a88, b88⟩ := step87 hw hφ n87 a87 b87
  obtain ⟨n89, a89, b89⟩ := step88 hw hφ n88 a88 b88
  obtain ⟨n90, a90, b90⟩ := step89 hw hφ n89 a89 b89
  obtain ⟨n91, a91, b91⟩ := step90 hw hφ n90 a90 b90
  obtain ⟨n92, a92, b92⟩ := step91 hw hφ n91 a91 b91
  exact ⟨n80, n92, a91, b91, b92⟩


end Checked.Math.GCerts
