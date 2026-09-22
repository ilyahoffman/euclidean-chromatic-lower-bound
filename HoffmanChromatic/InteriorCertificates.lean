import HoffmanChromatic.LogEnclosure
import HoffmanChromatic.RateCover
import HoffmanChromatic.SharpParameters

/-! The six interior endpoint inequalities, each valid on the stated s-box. -/
namespace HoffmanChromatic
set_option maxRecDepth 16384
set_option maxHeartbeats 0

private theorem log_six_042_Z :
    (1546048407723:ℝ)/2500000000000≤Real.log (partition01 tailA6 ((119:ℝ)/200)) ∧ Real.log (partition01 tailA6 ((119:ℝ)/200))≤(6184193630893:ℝ)/10000000000000 := by
  apply log_between_of_series (partition01 tailA6 ((119:ℝ)/200)) ((1855992072530889:ℝ)/1000000000000000) ((185599207253089:ℝ)/100000000000000) _ _ 30 30
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div,partition01,tailA6,Fin.sum_univ_succ]

private theorem log_six_042_x :
    (-2595969367183:ℝ)/5000000000000≤Real.log ((119:ℝ)/200) ∧ Real.log ((119:ℝ)/200)≤(-1038387746873:ℝ)/2000000000000 := by
  apply log_between_of_series ((119:ℝ)/200) ((119:ℝ)/200) ((119:ℝ)/200) _ _ 26 26
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div]

private theorem rate_six_042 :
    (2109077120067:ℝ)/2000000000000≤logarithmicRate (partition01 tailA6) ((21:ℝ)/25) ∧
    logarithmicRate (partition01 tailA6) ((21:ℝ)/25)≤(10545422167761:ℝ)/10000000000000 := by
  have h := logarithmicRate_numeric_bound tailA6 ((119:ℝ)/200) ((149:ℝ)/250) ((21:ℝ)/25)
    ((1546048407723:ℝ)/2500000000000) ((6184193630893:ℝ)/10000000000000) ((-2595969367183:ℝ)/5000000000000) ((-1038387746873:ℝ)/2000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ])
    (by norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ])
    log_six_042_Z log_six_042_x
  have hm : mean01 tailA6 ((119:ℝ)/200)=(50954080894828855818744713018946985:ℝ)/60817148232692173586508420867929799 := by
    norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ]
  rw [hm] at h
  norm_num at h
  constructor <;> linarith only [h.1,h.2]

private theorem log_six_055_Z :
    (7249727278373:ℝ)/10000000000000≤Real.log (partition01 tailA6 ((133:ℝ)/200)) ∧ Real.log (partition01 tailA6 ((133:ℝ)/200))≤(3624863639187:ℝ)/5000000000000 := by
  apply log_between_of_series (partition01 tailA6 ((133:ℝ)/200)) ((2064674791052027:ℝ)/1000000000000000) ((516168697763007:ℝ)/250000000000000) _ _ 34 34
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div,partition01,tailA6,Fin.sum_univ_succ]

private theorem log_six_055_x :
    (-4079682383263:ℝ)/10000000000000≤Real.log ((133:ℝ)/200) ∧ Real.log ((133:ℝ)/200)≤(-2039841191631:ℝ)/5000000000000 := by
  apply log_between_of_series ((133:ℝ)/200) ((133:ℝ)/200) ((133:ℝ)/200) _ _ 22 22
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div]

private theorem rate_six_055 :
    (5868678441963:ℝ)/5000000000000≤logarithmicRate (partition01 tailA6) ((11:ℝ)/10) ∧
    logarithmicRate (partition01 tailA6) ((11:ℝ)/10)≤(2934344474991:ℝ)/2500000000000 := by
  have h := logarithmicRate_numeric_bound tailA6 ((133:ℝ)/200) ((333:ℝ)/500) ((11:ℝ)/10)
    ((7249727278373:ℝ)/10000000000000) ((3624863639187:ℝ)/5000000000000) ((-4079682383263:ℝ)/10000000000000) ((-2039841191631:ℝ)/5000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ])
    (by norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ])
    log_six_055_Z log_six_055_x
  have hm : mean01 tailA6 ((133:ℝ)/200)=(24775412397077425153358815039934785:ℝ)/22551754517730941433955441002662319 := by
    norm_num [mean01,partition01,tailA6,Fin.sum_univ_succ]
  rw [hm] at h
  norm_num at h
  constructor <;> linarith only [h.1,h.2]

private theorem log_seven_055_Z :
    (7234122066879:ℝ)/10000000000000≤Real.log (partition01 tailA7 ((83:ℝ)/125)) ∧ Real.log (partition01 tailA7 ((83:ℝ)/125))≤(22606631459:ℝ)/31250000000 := by
  apply log_between_of_series (partition01 tailA7 ((83:ℝ)/125)) ((2061455335041873:ℝ)/1000000000000000) ((1030727667520937:ℝ)/500000000000000) _ _ 34 34
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div,partition01,tailA7,Fin.sum_univ_succ]

private theorem log_seven_055_x :
    (-2047365647529:ℝ)/5000000000000≤Real.log ((83:ℝ)/125) ∧ Real.log ((83:ℝ)/125)≤(-4094731295057:ℝ)/10000000000000 := by
  apply log_between_of_series ((83:ℝ)/125) ((83:ℝ)/125) ((83:ℝ)/125) _ _ 22 22
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div]

private theorem rate_seven_055 :
    (2934566327441:ℝ)/2500000000000≤logarithmicRate (partition01 tailA7) ((11:ℝ)/10) ∧
    logarithmicRate (partition01 tailA7) ((11:ℝ)/10)≤(2934581622861:ℝ)/2500000000000 := by
  have h := logarithmicRate_numeric_bound tailA7 ((83:ℝ)/125) ((133:ℝ)/200) ((11:ℝ)/10)
    ((7234122066879:ℝ)/10000000000000) ((22606631459:ℝ)/31250000000) ((-2047365647529:ℝ)/5000000000000) ((-4094731295057:ℝ)/10000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ])
    (by norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ])
    log_seven_055_Z log_seven_055_x
  have hm : mean01 tailA7 ((83:ℝ)/125)=(34992257753665440597427728524570406964564024:ℝ)/31929062181917612905236513733605154993569269 := by
    norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ]
  rw [hm] at h
  norm_num at h
  constructor <;> linarith only [h.1,h.2]

private theorem log_seven_068_Z :
    (507429977167:ℝ)/625000000000≤Real.log (partition01 tailA7 ((357:ℝ)/500)) ∧ Real.log (partition01 tailA7 ((357:ℝ)/500))≤(8118879634673:ℝ)/10000000000000 := by
  apply log_between_of_series (partition01 tailA7 ((357:ℝ)/500)) ((1126077981791973:ℝ)/500000000000000) ((2252155963583947:ℝ)/1000000000000000) _ _ 38 38
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div,partition01,tailA7,Fin.sum_univ_succ]

private theorem log_seven_068_x :
    (-1684361583213:ℝ)/5000000000000≤Real.log ((357:ℝ)/500) ∧ Real.log ((357:ℝ)/500)≤(-134748926657:ℝ)/400000000000 := by
  apply log_between_of_series ((357:ℝ)/500) ((357:ℝ)/500) ((357:ℝ)/500) _ _ 20 20
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div]

private theorem rate_seven_068 :
    (12700318016077:ℝ)/10000000000000≤logarithmicRate (partition01 tailA7) ((34:ℝ)/25) ∧
    logarithmicRate (partition01 tailA7) ((34:ℝ)/25)≤(12700343141013:ℝ)/10000000000000 := by
  have h := logarithmicRate_numeric_bound tailA7 ((357:ℝ)/500) ((143:ℝ)/200) ((34:ℝ)/25)
    ((507429977167:ℝ)/625000000000) ((8118879634673:ℝ)/10000000000000) ((-1684361583213:ℝ)/5000000000000) ((-134748926657:ℝ)/400000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ])
    (by norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ])
    log_seven_068_Z log_seven_068_x
  have hm : mean01 tailA7 ((357:ℝ)/500)=(1458593331542374170189405031960490919005421557833683493497:ℝ)/1073911649505589625065436102120896747838173347992080166357 := by
    norm_num [mean01,partition01,tailA7,Fin.sum_univ_succ]
  rw [hm] at h
  norm_num at h
  constructor <;> linarith only [h.1,h.2]

private theorem log_interior_1_Z :
    (1668963213627:ℝ)/5000000000000≤Real.log (partition01 tailE6 ((342211:ℝ)/1000000)) ∧ Real.log (partition01 tailE6 ((342211:ℝ)/1000000))≤(667585285451:ℝ)/2000000000000 := by
  apply log_between_of_series (partition01 tailE6 ((342211:ℝ)/1000000)) ((698126795107997:ℝ)/500000000000000) ((279250718043199:ℝ)/200000000000000) _ _ 20 20
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div,partition01,tailE6,Fin.sum_univ_succ]

private theorem log_interior_1_s :
    (-670208510913:ℝ)/625000000000≤Real.log ((342209:ℝ)/1000000) ∧ Real.log ((342209:ℝ)/1000000)≤(-10723336174607:ℝ)/10000000000000 := by
  apply log_between_of_series ((342209:ℝ)/1000000) ((342209:ℝ)/1000000) ((342209:ℝ)/1000000) _ _ 50 50
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div]

theorem interior_minorant_1 (s : ℝ)
    (hsl : (342209:ℝ)/1000000≤s) (hsu : s≤(342211:ℝ)/1000000) :
    (54073:ℝ)/200000<rateMinorant tailA6 tailE6 s ((21:ℝ)/50) := by
  have hA : (2109077120067:ℝ)/2000000000000≤logarithmicRate (partition01 tailA6) (2*((21:ℝ)/50)) := by
    convert rate_six_042.1 using 1; norm_num
  have h := rateMinorant_box_lower tailA6 tailE6 ((21:ℝ)/50) s ((342209:ℝ)/1000000) ((342211:ℝ)/1000000)
    ((2109077120067:ℝ)/2000000000000) ((667585285451:ℝ)/2000000000000) ((-670208510913:ℝ)/625000000000) (by norm_num) (by norm_num) hsl hsu
    hA log_interior_1_Z.2 log_interior_1_s.1
  linarith only [h]

private theorem log_interior_2_Z :
    (3991233777771:ℝ)/10000000000000≤Real.log (partition01 tailE6 ((2:ℝ)/5)) ∧ Real.log (partition01 tailE6 ((2:ℝ)/5))≤(997808444443:ℝ)/2500000000000 := by
  apply log_between_of_series (partition01 tailE6 ((2:ℝ)/5)) ((2911167:ℝ)/1953125) ((2911167:ℝ)/1953125) _ _ 22 22
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div,partition01,tailE6,Fin.sum_univ_succ]

private theorem log_interior_2_s :
    (-4581453659371:ℝ)/5000000000000≤Real.log ((2:ℝ)/5) ∧ Real.log ((2:ℝ)/5)≤(-9162907318741:ℝ)/10000000000000 := by
  apply log_between_of_series ((2:ℝ)/5) ((2:ℝ)/5) ((2:ℝ)/5) _ _ 42 42
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div]

theorem interior_minorant_2 (s : ℝ)
    (hsl : (2:ℝ)/5≤s) (hsu : s≤(2:ℝ)/5) :
    (270573:ℝ)/1000000<rateMinorant tailA6 tailE6 s ((21:ℝ)/50) := by
  have hA : (2109077120067:ℝ)/2000000000000≤logarithmicRate (partition01 tailA6) (2*((21:ℝ)/50)) := by
    convert rate_six_042.1 using 1; norm_num
  have h := rateMinorant_box_lower tailA6 tailE6 ((21:ℝ)/50) s ((2:ℝ)/5) ((2:ℝ)/5)
    ((2109077120067:ℝ)/2000000000000) ((997808444443:ℝ)/2500000000000) ((-4581453659371:ℝ)/5000000000000) (by norm_num) (by norm_num) hsl hsu
    hA log_interior_2_Z.2 log_interior_2_s.1
  linarith only [h]

theorem interior_minorant_3 (s : ℝ)
    (hsl : (2:ℝ)/5≤s) (hsu : s≤(2:ℝ)/5) :
    (67663:ℝ)/250000<rateMinorant tailA6 tailE6 s ((11:ℝ)/20) := by
  have hA : (5868678441963:ℝ)/5000000000000≤logarithmicRate (partition01 tailA6) (2*((11:ℝ)/20)) := by
    convert rate_six_055.1 using 1; norm_num
  have h := rateMinorant_box_lower tailA6 tailE6 ((11:ℝ)/20) s ((2:ℝ)/5) ((2:ℝ)/5)
    ((5868678441963:ℝ)/5000000000000) ((997808444443:ℝ)/2500000000000) ((-4581453659371:ℝ)/5000000000000) (by norm_num) (by norm_num) hsl hsu
    hA log_interior_2_Z.2 log_interior_2_s.1
  linarith only [h]

private theorem log_interior_4_Z :
    (4996585032081:ℝ)/10000000000000≤Real.log (partition01 tailE7 ((12:ℝ)/25)) ∧ Real.log (partition01 tailE7 ((12:ℝ)/25))≤(2498292516041:ℝ)/5000000000000 := by
  apply log_between_of_series (partition01 tailE7 ((12:ℝ)/25)) ((1648158333801621:ℝ)/1000000000000000) ((824079166900811:ℝ)/500000000000000) _ _ 26 26
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div,partition01,tailE7,Fin.sum_univ_succ]

private theorem log_interior_4_s :
    (-7339691750803:ℝ)/10000000000000≤Real.log ((12:ℝ)/25) ∧ Real.log ((12:ℝ)/25)≤(-3669845875401:ℝ)/5000000000000 := by
  apply log_between_of_series ((12:ℝ)/25) ((12:ℝ)/25) ((12:ℝ)/25) _ _ 34 34
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div]

theorem interior_minorant_4 (s : ℝ)
    (hsl : (12:ℝ)/25≤s) (hsu : s≤(12:ℝ)/25) :
    (67621:ℝ)/250000<rateMinorant tailA7 tailE7 s ((11:ℝ)/20) := by
  have hA : (2934566327441:ℝ)/2500000000000≤logarithmicRate (partition01 tailA7) (2*((11:ℝ)/20)) := by
    convert rate_seven_055.1 using 1; norm_num
  have h := rateMinorant_box_lower tailA7 tailE7 ((11:ℝ)/20) s ((12:ℝ)/25) ((12:ℝ)/25)
    ((2934566327441:ℝ)/2500000000000) ((2498292516041:ℝ)/5000000000000) ((-7339691750803:ℝ)/10000000000000) (by norm_num) (by norm_num) hsl hsu
    hA log_interior_4_Z.2 log_interior_4_s.1
  linarith only [h]

theorem interior_minorant_5 (s : ℝ)
    (hsl : (12:ℝ)/25≤s) (hsu : s≤(12:ℝ)/25) :
    (135637:ℝ)/500000<rateMinorant tailA7 tailE7 s ((17:ℝ)/25) := by
  have hA : (12700318016077:ℝ)/10000000000000≤logarithmicRate (partition01 tailA7) (2*((17:ℝ)/25)) := by
    convert rate_seven_068.1 using 1; norm_num
  have h := rateMinorant_box_lower tailA7 tailE7 ((17:ℝ)/25) s ((12:ℝ)/25) ((12:ℝ)/25)
    ((12700318016077:ℝ)/10000000000000) ((2498292516041:ℝ)/5000000000000) ((-7339691750803:ℝ)/10000000000000) (by norm_num) (by norm_num) hsl hsu
    hA log_interior_4_Z.2 log_interior_4_s.1
  linarith only [h]

private theorem log_interior_6_Z :
    (5513872436573:ℝ)/10000000000000≤Real.log (partition01 tailE7 ((32327:ℝ)/62500)) ∧ Real.log (partition01 tailE7 ((32327:ℝ)/62500))≤(2756936218287:ℝ)/5000000000000 := by
  apply log_between_of_series (partition01 tailE7 ((32327:ℝ)/62500)) ((1735659130669437:ℝ)/1000000000000000) ((867829565334719:ℝ)/500000000000000) _ _ 28 28
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div,partition01,tailE7,Fin.sum_univ_succ]

private theorem log_interior_6_s :
    (-6592676291263:ℝ)/10000000000000≤Real.log ((51723:ℝ)/100000) ∧ Real.log ((51723:ℝ)/100000)≤(-3296338145631:ℝ)/5000000000000 := by
  apply log_between_of_series ((51723:ℝ)/100000) ((51723:ℝ)/100000) ((51723:ℝ)/100000) _ _ 32 32
  all_goals norm_num [logApprox,logTaylorSum,logEta,logError,Finset.sum_range_succ,abs_div]

theorem interior_minorant_6 (s : ℝ)
    (hsl : (51723:ℝ)/100000≤s) (hsu : s≤(32327:ℝ)/62500) :
    (135171:ℝ)/500000<rateMinorant tailA7 tailE7 s ((17:ℝ)/25) := by
  have hA : (12700318016077:ℝ)/10000000000000≤logarithmicRate (partition01 tailA7) (2*((17:ℝ)/25)) := by
    convert rate_seven_068.1 using 1; norm_num
  have h := rateMinorant_box_lower tailA7 tailE7 ((17:ℝ)/25) s ((51723:ℝ)/100000) ((32327:ℝ)/62500)
    ((12700318016077:ℝ)/10000000000000) ((2756936218287:ℝ)/5000000000000) ((-6592676291263:ℝ)/10000000000000) (by norm_num) (by norm_num) hsl hsu
    hA log_interior_6_Z.2 log_interior_6_s.1
  linarith only [h]

end HoffmanChromatic
