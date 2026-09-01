/- Axiom audit. Run after `lake build`:

     lake env lean Check.lean

   Every line of output must read
     '<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
   `scripts/audit.sh` asserts exactly that (and is run by CI).
-/
import P287.Main2
import P287.Lower3
import P287.Window4
import P287.Budget
import P287.Bertrand134
import P287.KFinal
import P287.gap_full
import P287.G3Ext
import P287.Cascade
import P287.APTwo
import P287.QLaw
import P287.IndepRank
import P287.IndepDual
import P287.AltChain
import P287.ParitySwitch
import P287.RoughChain
import P287.GapOne
import P287.Egyptian
import P287.Part3

#print axioms Main2.erdos287_below
#print axioms Kurschak.gap_at_least_two
#print axioms Kurschak.gap_at_least_two_upstream_shape
#print axioms PCI.prime_conjecture_implies
#print axioms Lower3.lower3
#print axioms Window4.window4
#print axioms KFinal.kbound
#print axioms Bertrand134.g1_ge_134
#print axioms G3Ext.g3_all_ext
#print axioms Budget.budget
#print axioms Cascade.cascade
#print axioms APTwo.no_ap2
#print axioms QLaw.qlaw
#print axioms IndepRank.sum_inv_ge
#print axioms IndepRank.card_le
#print axioms IndepDual.sum_inv_le
#print axioms AltChain.card_le_of_alt_chain
#print axioms ParitySwitch.card_le_of_mixed_parity
#print axioms RoughChain.g1_ge_of_free_prime
#print axioms GapOne.g1_add_compl_card
#print axioms Egyptian.largest_not_prime
#print axioms Egyptian.largest_not_prime_power
#print axioms Egyptian.cofactor_bound
