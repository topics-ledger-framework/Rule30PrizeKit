module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift

/-! Certificate data for the tail-97 completion. A punctured width-26
cycle (`L = 8192`, single bad index `6313`) and 32 parallel upper states
certify a width-36 return cycle (`H = 262144`, post-arrival horizon `35`). -/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30Tail97Completion
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

def lanes : Nat := 2^32-1

def seeds : List Nat := [0,961,114,635,392,9,602,323,32,481,274,475,872,233,698,803,640,321,754,763,8,905,474,195,672,353,658,347,488,361,826,931]

def embedding (j : Nat) : Nat := 97 ||| (seeds.getD j 0 <<< 26)

def nextIndex (j : Nat) : Nat := (j+1)%32

def state000 : LaneState := ⟨97, 0, [0xaaaaaaaa, 0xcccccccc, 0x0, 0x78787878, 0x4c4c4c4c, 0xf30cf30c, 0x3ace3ace, 0x95ed6a12, 0xfa629e92, 0xc52dd04a]⟩

def state001 : LaneState := ⟨58411606, 1, [0x55555555, 0x99999999, 0xeeeeeeee, 0x78787878, 0x37373737, 0xc33cc33c, 0xee9fee9f, 0xde1421eb, 0xe4709d0f, 0x38f976e5]⟩

def state002 : LaneState := ⟨97, 0, [0x55555555, 0x66666666, 0x0, 0x3c3c3c3c, 0x26262626, 0x79867986, 0x1d671d67, 0x4af6b509, 0x7d314f49, 0x6296e825]⟩

def r00_st001 : LaneState := ⟨46681185, 0, [0xaaaaaaaa, 0x33333333, 0x66666666, 0x5a5a5a5a, 0x7a7a7a7a, 0xba45ba45, 0xb845b845, 0x8b677498, 0xdea88733, 0x8796f031]⟩
def r00_st002 : LaneState := ⟨52533345, 0, [0x55555555, 0x99999999, 0x33333333, 0x4b4b4b4b, 0x6d6d6d6d, 0xc53ac53a, 0xbc60bc60, 0x927b6d84, 0xefdc7587, 0x520e1601]⟩
def r00_st003 : LaneState := ⟨31855713, 0, [0x55555555, 0x66666666, 0x55555555, 0xe1e1e1e1, 0x2a2a2a2a, 0x1ce31ce3, 0xb682b682, 0x5633a9cc, 0xaa741517, 0x3d55a1f4]⟩
def r00_st004 : LaneState := ⟨56655969, 0, [0xaaaaaaaa, 0x99999999, 0xaaaaaaaa, 0x78787878, 0x26262626, 0x32cd32cd, 0x4a7e4a7e, 0x10c6ef39, 0x20aa432c, 0x22413a62]⟩
def r00_st005 : LaneState := ⟨2280545, 0, [0xaaaaaaaa, 0x33333333, 0x55555555, 0x78787878, 0x5b5b5b5b, 0x52ad52ad, 0x44d044d, 0x583ea7c1, 0x4df71733, 0x253ee20a]⟩
def r00_st006 : LaneState := ⟨399457, 0, [0x55555555, 0x33333333, 0x99999999, 0x4b4b4b4b, 0xdadadada, 0x7f807f8, 0xda27da27, 0x86b0794f, 0x9475f281, 0xd4799cd9]⟩
def r00_st007 : LaneState := ⟨49452129, 0, [0xaaaaaaaa, 0x66666666, 0x99999999, 0xf0f0f0f0, 0x43434343, 0x43bc43bc, 0x1f061f06, 0xa2925d6d, 0xa34e596e, 0x8e6f5e6a]⟩
def r00_st008 : LaneState := ⟨61997153, 0, [0x55555555, 0x99999999, 0x33333333, 0x96969696, 0x23232323, 0x23dc23dc, 0x17921792, 0xe74718b8, 0xe3b50b35, 0x2b6902c3]⟩
def r00_st009 : LaneState := ⟨45501537, 0, [0x55555555, 0x33333333, 0x33333333, 0xa5a5a5a5, 0x86868686, 0xc13ec13e, 0x94db94db, 0x3b8ec471, 0x5d3c3276, 0x626f359b]⟩
def r00_st010 : LaneState := ⟨6264929, 0, [0x55555555, 0x66666666, 0x0, 0x69696969, 0x79797979, 0x1ee11ee1, 0x14b914b9, 0xf82f07d0, 0xa5d2d9be, 0x49e30551]⟩
def r00_st011 : LaneState := ⟨47453281, 0, [0x55555555, 0xcccccccc, 0x66666666, 0x96969696, 0x76767676, 0x1fe01fe, 0x30df30df, 0xd2752d8a, 0xa310a3b7, 0x76d392b4]⟩
def r00_st012 : LaneState := ⟨20349025, 0, [0x55555555, 0x66666666, 0xcccccccc, 0xc3c3c3c3, 0xfefefefe, 0xa25da25d, 0x49d249d2, 0x233ddcc2, 0xb496597, 0xa7fbd442]⟩
def r00_st013 : LaneState := ⟨49859681, 0, [0xaaaaaaaa, 0xcccccccc, 0xcccccccc, 0x1e1e1e1e, 0xb3b3b3b3, 0xa956a956, 0x3b663b66, 0x2fead015, 0x25e6897e, 0x629d656d]⟩
def r00_st014 : LaneState := ⟨14686305, 0, [0x55555555, 0x66666666, 0x66666666, 0xe1e1e1e1, 0xfefefefe, 0x619e619e, 0x382e382e, 0xbf2740d8, 0x234c188a, 0xbffe9397]⟩
def r00_st015 : LaneState := ⟨22582369, 0, [0x55555555, 0x33333333, 0x99999999, 0x3c3c3c3c, 0x58585858, 0xce31ce31, 0x4c604c6, 0xbc1243ed, 0x596273a7, 0x44bbc536]⟩
def r00_st016 : LaneState := ⟨53739617, 0, [0xaaaaaaaa, 0xcccccccc, 0x66666666, 0x4b4b4b4b, 0x92929292, 0xae51ae51, 0xa03da03d, 0xb4d44b2b, 0xf3f96f73, 0xc09090a5]⟩
def r00_st017 : LaneState := ⟨24923233, 0, [0x55555555, 0x33333333, 0xaaaaaaaa, 0x87878787, 0x45454545, 0xca35ca35, 0xbeb0beb, 0x610f9ef, 0x59a29785, 0xd88e88b]⟩
def r00_st018 : LaneState := ⟨43358305, 0, [0x55555555, 0x99999999, 0xcccccccc, 0xf0f0f0f, 0xefefefef, 0x9d629d62, 0x44ce44ce, 0x56b7a948, 0x1ca7fdc0, 0xc619f74c]⟩
def r00_st019 : LaneState := ⟨66720865, 0, [0x55555555, 0x66666666, 0xffffffff, 0xb4b4b4b4, 0xbabababa, 0x7b847b84, 0x82b082b, 0x10c6ef39, 0x483bea23, 0x44e50bdc]⟩
def r00_st020 : LaneState := ⟨6062177, 0, [0x55555555, 0x33333333, 0x55555555, 0x87878787, 0xa2a2a2a2, 0x4fb04fb, 0x5bd85bd8, 0x86e2791d, 0xb263acb5, 0x97101d61]⟩
def r00_st021 : LaneState := ⟨59165793, 0, [0xaaaaaaaa, 0x99999999, 0x0, 0xf0f0f0f, 0x9b9b9b9b, 0x609f609f, 0x492d492d, 0xbf3540ca, 0x2ffa929b, 0x54806a66]⟩
def r00_st022 : LaneState := ⟨56760417, 0, [0x55555555, 0xcccccccc, 0x66666666, 0xc3c3c3c3, 0x2020202, 0x54ab54ab, 0x27042704, 0x5e18a1e7, 0xe5c009e8, 0x741a69a8]⟩
def r00_st023 : LaneState := ⟨25597025, 0, [0x55555555, 0xcccccccc, 0x99999999, 0x5a5a5a5a, 0x67676767, 0x66996699, 0x758d758d, 0x1238edc7, 0x2c99240a, 0x930dd366]⟩
def r00_st024 : LaneState := ⟨55443553, 0, [0x55555555, 0x66666666, 0x33333333, 0x69696969, 0x80808080, 0xd629d629, 0xf9d9f9d9, 0x34a6cb59, 0xb1bebf96, 0x38f8a0ac]⟩
def r00_st025 : LaneState := ⟨22695009, 0, [0xaaaaaaaa, 0xcccccccc, 0x99999999, 0x3c3c3c3c, 0x46464646, 0x8e718e71, 0xf27bf27b, 0x3023cfdc, 0xc00b8ec9, 0x3a828a3a]⟩
def r00_st026 : LaneState := ⟨25401441, 0, [0xaaaaaaaa, 0x66666666, 0x55555555, 0xc3c3c3c3, 0x4f4f4f4f, 0x1ae51ae5, 0x7e3b7e3b, 0xf0c00f3f, 0xfca0cb8b, 0x4cbbc3b5]⟩
def r00_st027 : LaneState := ⟨17831009, 0, [0xaaaaaaaa, 0x66666666, 0x0, 0x78787878, 0x26262626, 0x1de21de2, 0x75187518, 0x50feaf01, 0x19a41a7b, 0xb20b41b5]⟩
def r00_st028 : LaneState := ⟨27426913, 0, [0x55555555, 0x66666666, 0xaaaaaaaa, 0xd2d2d2d2, 0x61616161, 0x9a659a65, 0xac91ac91, 0x4a61b59e, 0xfa0f9015, 0xbee209ae]⟩
def r00_st029 : LaneState := ⟨33868897, 0, [0xaaaaaaaa, 0x99999999, 0x33333333, 0xb4b4b4b4, 0xf8f8f8f8, 0x5fa05fa, 0x1b4f1b4f, 0xce3931c6, 0x3851ef78, 0xfc55dd5e]⟩
def r00_st030 : LaneState := ⟨15472737, 0, [0xaaaaaaaa, 0xcccccccc, 0xcccccccc, 0x5a5a5a5a, 0xe6e6e6e6, 0x6a956a95, 0x63196319, 0xb9a4465b, 0x33209374, 0xf3a07cb]⟩
def r00_st031 : LaneState := ⟨1348705, 0, [0x55555555, 0x33333333, 0x0, 0xb4b4b4b4, 0x83838383, 0x837c837c, 0xac34ac34, 0xbfef4010, 0x3cbf08ba, 0x65ad1ebb]⟩
def r00_st032 : LaneState := ⟨12583009, 0, [0xaaaaaaaa, 0x66666666, 0xffffffff, 0x4b4b4b4b, 0xeaeaeaea, 0x4db24db2, 0xb461b461, 0x98ff67, 0x3bf2cbf5, 0xad8db226]⟩
def r00_st033 : LaneState := ⟨17321057, 0, [0x55555555, 0x66666666, 0xaaaaaaaa, 0x78787878, 0xb0b0b0b, 0xbf40bf40, 0xdfb4dfb4, 0xf93f06c, 0xb15bf87, 0x7ea1e323]⟩
def r00_st034 : LaneState := ⟨31561825, 0, [0x55555555, 0x99999999, 0x99999999, 0x4b4b4b4b, 0x1f1f1f1f, 0xad52ad52, 0xccb0ccb0, 0x62e49d1b, 0xcd6be38e, 0x3d4001fe]⟩
def r00_st035 : LaneState := ⟨44438625, 0, [0xaaaaaaaa, 0xcccccccc, 0x99999999, 0x2d2d2d2d, 0x8f8f8f8f, 0xab54ab54, 0x3910391, 0x1e0ee1f1, 0xf5570f3f, 0xdd0c0cfb]⟩
def r00_st036 : LaneState := ⟨2130017, 0, [0xaaaaaaaa, 0x33333333, 0xcccccccc, 0xc3c3c3c3, 0xf8f8f8f8, 0xb24db24d, 0xf850f85, 0x1958e6a7, 0x72533ae6, 0xfde98c6d]⟩
def r00_st037 : LaneState := ⟨65195105, 0, [0x55555555, 0xcccccccc, 0x0, 0xc3c3c3c3, 0xf7f7f7f7, 0xce31ce31, 0x16651665, 0xef2710d8, 0x196be4a4, 0x23539c02]⟩
def r00_st038 : LaneState := ⟨29759585, 0, [0x55555555, 0x66666666, 0xaaaaaaaa, 0x3c3c3c3c, 0xb9b9b9b9, 0xe817e817, 0x1f501f5, 0x9f1460eb, 0xdd2a50fc, 0x392dd716]⟩
def r00_st039 : LaneState := ⟨62035041, 0, [0xaaaaaaaa, 0x33333333, 0x0, 0x5a5a5a5a, 0x4f4f4f4f, 0xcc33cc33, 0x96839683, 0x92f36d0c, 0x999b92da, 0x5c169e53]⟩
def r00_st040 : LaneState := ⟨24248417, 0, [0xaaaaaaaa, 0x99999999, 0x99999999, 0x1e1e1e1e, 0xe0e0e0e0, 0xa05fa05f, 0x9a7c9a7c, 0x5862a79d, 0x31a15f0b, 0xcbe6d36]⟩
def r00_st041 : LaneState := ⟨49695841, 0, [0x55555555, 0xcccccccc, 0x99999999, 0x5a5a5a5a, 0xbcbcbcbc, 0x46b946b9, 0x42a242a2, 0xfe690196, 0x7bda2bc9, 0x5b4b0bca]⟩
def r00_st042 : LaneState := ⟨2070625, 0, [0xaaaaaaaa, 0xcccccccc, 0x0, 0xb4b4b4b4, 0xa1a1a1a1, 0x4cb34cb3, 0xc09ec09e, 0xcd74328b, 0x6a096e8e, 0x1fa163a9]⟩
def r00_st043 : LaneState := ⟨51647585, 0, [0xaaaaaaaa, 0x33333333, 0x99999999, 0x96969696, 0xb5b5b5b5, 0xf609f609, 0x4a904a90, 0x232ddcd2, 0x1680e053, 0xb443f76c]⟩
def r00_st044 : LaneState := ⟨66486369, 0, [0xaaaaaaaa, 0x33333333, 0x55555555, 0xb4b4b4b4, 0xd3d3d3d3, 0x10ef10ef, 0xcea6cea6, 0x1a9ae565, 0x908a0cc3, 0xc9babdcf]⟩
def r00_st045 : LaneState := ⟨28888161, 0, [0xaaaaaaaa, 0x99999999, 0xaaaaaaaa, 0xb4b4b4b4, 0xfdfdfdfd, 0x2ad52ad5, 0x9e829e82, 0xa2f15d0e, 0x73f1f301, 0xcf734205]⟩
def r00_st046 : LaneState := ⟨60823649, 0, [0xaaaaaaaa, 0x99999999, 0x0, 0x87878787, 0x1c1c1c1c, 0xa45ba45b, 0x10cc10cc, 0xa72158de, 0x677caae6, 0xebcb5362]⟩
def r00_st047 : LaneState := ⟨35165281, 0, [0x55555555, 0x66666666, 0x66666666, 0x96969696, 0xb6b6b6b6, 0xbf40bf40, 0x44974497, 0xecbd1342, 0x2394992, 0xb7985f44]⟩
def r00_st048 : LaneState := ⟨41156705, 0, [0x55555555, 0x99999999, 0x55555555, 0x3c3c3c3c, 0x25252525, 0xbe41be41, 0xd93cd93c, 0x1550eaaf, 0x362e0763, 0x9d467eae]⟩
def r00_st049 : LaneState := ⟨37506145, 0, [0x55555555, 0x99999999, 0xffffffff, 0x96969696, 0xa2a2a2a2, 0x89768976, 0xee3bee3b, 0xf83107ce, 0x275954cf, 0xe4b633c9]⟩
def r00_st050 : LaneState := ⟨30775393, 0, [0x55555555, 0x99999999, 0x33333333, 0x4b4b4b4b, 0xbfbfbfbf, 0xbe41be41, 0xcafecafe, 0xe82317dc, 0x5a6846c8, 0xffb2f6a2]⟩
def r00_st051 : LaneState := ⟨62526561, 0, [0xaaaaaaaa, 0x33333333, 0x66666666, 0x96969696, 0x31313131, 0xff00ff, 0x42804280, 0xd80a27f5, 0x26325e96, 0x3e0c85c]⟩
def r00_st052 : LaneState := ⟨60588129, 0, [0xaaaaaaaa, 0x99999999, 0x33333333, 0x69696969, 0x10101010, 0xa55aa55a, 0xc760c76, 0xd3292cd6, 0xd44b692f, 0x1c115753]⟩
def r00_st053 : LaneState := ⟨54971489, 0, [0xaaaaaaaa, 0x99999999, 0xffffffff, 0xc3c3c3c3, 0xc2c2c2c2, 0x11ee11ee, 0xee8cee8c, 0x9e9d6162, 0x8e500907, 0xc0262e57]⟩
def r00_st054 : LaneState := ⟨27400289, 0, [0x55555555, 0x66666666, 0xaaaaaaaa, 0x4b4b4b4b, 0x2a2a2a2a, 0xeb14eb14, 0x6f046f04, 0xb3184ce7, 0xbd31fc71, 0xd669794]⟩
def r00_st055 : LaneState := ⟨63345761, 0, [0xaaaaaaaa, 0x33333333, 0xaaaaaaaa, 0xe1e1e1e1, 0x61616161, 0x8d728d72, 0xcba6cba6, 0x84ea7b15, 0x1a41fc87, 0x628b3636]⟩
def r00_st056 : LaneState := ⟨42860641, 0, [0xaaaaaaaa, 0x99999999, 0x55555555, 0x69696969, 0x4f4f4f4f, 0x98679867, 0xd5c6d5c6, 0x662299dd, 0x3870a33e, 0xaf368107]⟩
def r00_st057 : LaneState := ⟨43666529, 0, [0x55555555, 0xcccccccc, 0xffffffff, 0xb4b4b4b4, 0xd9d9d9d9, 0xa956a956, 0x983c983c, 0xba5b45a4, 0xbedcbc85, 0xa9c24b4]⟩
def r00_st058 : LaneState := ⟨37984353, 0, [0x55555555, 0xcccccccc, 0x0, 0x78787878, 0x68686868, 0xc13ec13e, 0x3bbe3bbe, 0xba8f457, 0x69b479c5, 0xc118aa45]⟩
def r00_st059 : LaneState := ⟨5248097, 0, [0xaaaaaaaa, 0x99999999, 0x55555555, 0x69696969, 0x20202020, 0xac53ac53, 0x8330833, 0xc95736a8, 0xa9e3390, 0x5d77c59d]⟩
def r00_st060 : LaneState := ⟨65175649, 0, [0xaaaaaaaa, 0x66666666, 0xaaaaaaaa, 0x78787878, 0x7f7f7f7f, 0x639c639c, 0x1c3f1c3f, 0x7e0181fe, 0xe4068a60, 0xcb00f50c]⟩
def r00_st061 : LaneState := ⟨29674593, 0, [0x55555555, 0x66666666, 0xcccccccc, 0x3c3c3c3c, 0xfbfbfbfb, 0xf807f807, 0x6cb06cb0, 0x65139aec, 0x62ffca0, 0xe5244b08]⟩
def r00_st062 : LaneState := ⟨11278433, 0, [0x55555555, 0xcccccccc, 0xffffffff, 0x87878787, 0xd0d0d0d0, 0x7b847b84, 0x5fa25fa2, 0x757f8a80, 0xf16ac99, 0xf99d6030]⟩
def r00_st063 : LaneState := ⟨39097441, 0, [0xaaaaaaaa, 0x66666666, 0x99999999, 0x2d2d2d2d, 0x70707070, 0x48b748b7, 0x76a376a3, 0x1de7e218, 0xb8545f71, 0x709a70b0]⟩
def r00_st064 : LaneState := ⟨58720353, 0, [0x55555555, 0x33333333, 0x99999999, 0x96969696, 0xdadadada, 0x49b649b6, 0x48944894, 0x6b4994b6, 0x45b434fb, 0xab0ce20e]⟩
def r00_st065 : LaneState := ⟨55069793, 0, [0xaaaaaaaa, 0x33333333, 0xaaaaaaaa, 0x69696969, 0x8c8c8c8c, 0xf10ef10e, 0xf6d0f6d, 0xc8763789, 0x125a091f, 0xf544b235]⟩
def r00_st066 : LaneState := ⟨44144737, 0, [0x55555555, 0x99999999, 0x55555555, 0x69696969, 0x6e6e6e6e, 0x8b748b74, 0x2dba2dba, 0xfd4202bd, 0x8af25a1c, 0x5cd60453]⟩
def r00_st067 : LaneState := ⟨57021537, 0, [0x55555555, 0xcccccccc, 0x99999999, 0xf0f0f0f0, 0x76767676, 0x35ca35ca, 0x9ada9ada, 0xcb5534aa, 0x31ae7ba2, 0xbde339d9]⟩
def r00_st068 : LaneState := ⟨31490145, 0, [0x55555555, 0x66666666, 0x33333333, 0xe1e1e1e1, 0x9d9d9d9d, 0xd827d827, 0xd59ad59a, 0xa3b25c4d, 0x7cee6d75, 0x9308f974]⟩
def r00_st069 : LaneState := ⟨27446369, 0, [0xaaaaaaaa, 0xcccccccc, 0x55555555, 0x5a5a5a5a, 0x4040404, 0x77887788, 0xba2eba2e, 0xba75458a, 0xa448dcae, 0x485e3f9b]⟩
def r00_st070 : LaneState := ⟨25565281, 0, [0x55555555, 0x66666666, 0x55555555, 0xe1e1e1e1, 0x15151515, 0x13ec13ec, 0x321b321b, 0x44adbb52, 0x4cb293f9, 0x9232089b]⟩
def r00_st071 : LaneState := ⟨7509089, 0, [0x55555555, 0x99999999, 0x66666666, 0x5a5a5a5a, 0x37373737, 0x6f906f9, 0xcfa7cfa7, 0xe66f199, 0x60e66bd9, 0x677eeb59]⟩
def r00_st072 : LaneState := ⟨53608545, 0, [0x55555555, 0x33333333, 0x66666666, 0x3c3c3c3c, 0xdcdcdcdc, 0x40bf40bf, 0xdd70dd70, 0x3298cd67, 0x240070d2, 0x20a9992d]⟩
def r00_st073 : LaneState := ⟨3558497, 0, [0x55555555, 0x33333333, 0x33333333, 0x78787878, 0xb0b0b0b0, 0x27d827d8, 0x37f037f0, 0xbe5641a9, 0x49f42115, 0xac7291fe]⟩
def r00_st074 : LaneState := ⟨48207969, 0, [0x55555555, 0xcccccccc, 0xffffffff, 0x1e1e1e1e, 0xa4a4a4a4, 0x639c639c, 0x6d3a6d3a, 0x8d74728b, 0x75c399c3, 0xd33784f]⟩
def r00_st075 : LaneState := ⟨5510241, 0, [0x55555555, 0x66666666, 0x33333333, 0xf0f0f0f, 0xc1c1c1c1, 0xe41be41b, 0x11231123, 0xcb0834f7, 0x719302c9, 0x8fddc08e]⟩
def r00_st076 : LaneState := ⟨28737633, 0, [0x55555555, 0x33333333, 0x99999999, 0x5a5a5a5a, 0x97979797, 0xce31ce31, 0xb36fb36f, 0x44d4bb2b, 0x9e359a59, 0xdbde8629]⟩
def r00_st077 : LaneState := ⟨24693857, 0, [0x55555555, 0x99999999, 0x0, 0xb4b4b4b4, 0x57575757, 0x68976897, 0x58a058a, 0xc33d3cc2, 0x99a734c1, 0x42e01cba]⟩
def r00_st078 : LaneState := ⟨56629345, 0, [0xaaaaaaaa, 0x99999999, 0xaaaaaaaa, 0xd2d2d2d2, 0x7f7f7f7f, 0x20df20df, 0xa5c4a5c4, 0xe1051efa, 0xd7146212, 0x7c4c0659]⟩
def r00_st079 : LaneState := ⟨64525409, 0, [0xaaaaaaaa, 0xcccccccc, 0xaaaaaaaa, 0x78787878, 0xabababab, 0x45ba45ba, 0xd6c6d6c6, 0x741f8be0, 0x459b62a, 0x45141b74]⟩
def r00_st080 : LaneState := ⟨11796577, 0, [0xaaaaaaaa, 0x33333333, 0x0, 0x78787878, 0x25252525, 0xca35ca35, 0xdea8dea8, 0x21d2de2d, 0x8a144e2e, 0xb21b7bc3]⟩
def r00_st081 : LaneState := ⟨50089057, 0, [0xaaaaaaaa, 0x99999999, 0x0, 0x96969696, 0xd0d0d0d, 0xf30cf30c, 0xa421a421, 0xddbe2241, 0xa32123cc, 0x8b9a700d]⟩
def r00_st082 : LaneState := ⟨34969697, 0, [0xaaaaaaaa, 0xcccccccc, 0x55555555, 0xf0f0f0f, 0x2c2c2c2c, 0x45ba45ba, 0xc417c417, 0xe4eb1b14, 0x4ea8618a, 0x656b8c4c]⟩
def r00_st083 : LaneState := ⟨24777825, 0, [0xaaaaaaaa, 0x66666666, 0xaaaaaaaa, 0xd2d2d2d2, 0x83838383, 0xc43bc43b, 0x433a433a, 0xa29e5d61, 0xd599494f, 0xfd36c321]⟩
def r00_st084 : LaneState := ⟨64782433, 0, [0xaaaaaaaa, 0x99999999, 0x33333333, 0x1e1e1e1e, 0xc2c2c2c2, 0x3ac53ac5, 0x3fc83fc8, 0x1d38e2c7, 0xb58b9959, 0xebbbec1a]⟩
def r00_st085 : LaneState := ⟨17222753, 0, [0x55555555, 0x66666666, 0x66666666, 0x4b4b4b4b, 0x1010101, 0xc23dc23d, 0xbca5bca5, 0x1b76e489, 0xa91d8303, 0x639eb6ba]⟩
def r00_st086 : LaneState := ⟨65149025, 0, [0x55555555, 0xcccccccc, 0x99999999, 0x87878787, 0x9e9e9e9e, 0x748b748b, 0x247c247c, 0xfdac0253, 0xed399760, 0x886dde7c]⟩
def r00_st087 : LaneState := ⟨50762849, 0, [0x55555555, 0x33333333, 0xffffffff, 0xe1e1e1e1, 0x3d3d3d3d, 0xb748b748, 0xc100c1, 0xafa85057, 0x17cbdccb, 0x3975305f]⟩
def r00_st088 : LaneState := ⟨13500513, 0, [0x55555555, 0x99999999, 0x66666666, 0x69696969, 0xdfdfdfdf, 0x3bc43bc4, 0x406f406f, 0xf6970968, 0x3eeef7d9, 0xfd2429e0]⟩
def r00_st089 : LaneState := ⟨31083617, 0, [0x55555555, 0x33333333, 0xffffffff, 0xc3c3c3c3, 0xe3e3e3e3, 0x21de21de, 0x809a809a, 0x92fe6d01, 0x8c313b2b, 0x4106dc84]⟩
def r00_st090 : LaneState := ⟨17012833, 0, [0x55555555, 0x33333333, 0x99999999, 0xb4b4b4b4, 0xb0b0b0b0, 0xdc23dc23, 0xdf42df42, 0xeebc1143, 0x1b40f126, 0x381dd3a]⟩
def r00_st091 : LaneState := ⟨42996833, 0, [0xaaaaaaaa, 0x99999999, 0x33333333, 0x87878787, 0x31313131, 0xf708f708, 0x39403940, 0xbe3341cc, 0xdae0c932, 0x97a6fb2d]⟩
def r00_st092 : LaneState := ⟨52592737, 0, [0xaaaaaaaa, 0x33333333, 0xaaaaaaaa, 0x96969696, 0xabababab, 0xd22dd22d, 0xb16db16d, 0x74ff8b00, 0x957e203a, 0x3e48cff0]⟩
def r00_st093 : LaneState := ⟨59034721, 0, [0x55555555, 0x33333333, 0xcccccccc, 0xf0f0f0f, 0xdcdcdcdc, 0xbe41be41, 0x72137213, 0x6e4691b9, 0x1d257ed1, 0xb6e0b8fd]⟩
def r00_st094 : LaneState := ⟨40638561, 0, [0xaaaaaaaa, 0x99999999, 0x55555555, 0xf0f0f0f, 0xe0e0e0e, 0x609f609f, 0x1c4e1c4e, 0xf9e4061b, 0x972dd02f, 0x63073990]⟩
def r00_st095 : LaneState := ⟨60068961, 0, [0x55555555, 0x99999999, 0x55555555, 0x2d2d2d2d, 0x2c2c2c2c, 0x38c738c7, 0xb79db79d, 0x51edae12, 0x3f41f6e3, 0xfde1eb45]⟩
def r00_st096 : LaneState := ⟨37748833, 0, [0xaaaaaaaa, 0x99999999, 0x0, 0x1e1e1e1e, 0x75757575, 0x936c936c, 0x69766976, 0x2b94d46b, 0xa21a1479, 0x94ed55e0]⟩
def r00_st097 : LaneState := ⟨25709665, 0, [0x55555555, 0xcccccccc, 0x33333333, 0xa5a5a5a5, 0xd0d0d0d, 0xe21de21d, 0xfc6bfc6b, 0xb5ca4a35, 0xf30009d5, 0x5eadcfd2]⟩
def r00_st098 : LaneState := ⟨56727649, 0, [0x55555555, 0x99999999, 0x99999999, 0xc3c3c3c3, 0x92929292, 0x7a857a85, 0x57935793, 0x4f77b088, 0x53c54425, 0x853e5393]⟩

theorem r00_s000 : run 26 lanes 64 state000 = r00_st001 := by decide +kernel
theorem r00_s001 : run 26 lanes 64 r00_st001 = r00_st002 := by decide +kernel
theorem r00_s002 : run 26 lanes 64 r00_st002 = r00_st003 := by decide +kernel
theorem r00_s003 : run 26 lanes 64 r00_st003 = r00_st004 := by decide +kernel
theorem r00_s004 : run 26 lanes 64 r00_st004 = r00_st005 := by decide +kernel
theorem r00_s005 : run 26 lanes 64 r00_st005 = r00_st006 := by decide +kernel
theorem r00_s006 : run 26 lanes 64 r00_st006 = r00_st007 := by decide +kernel
theorem r00_s007 : run 26 lanes 64 r00_st007 = r00_st008 := by decide +kernel
theorem r00_s008 : run 26 lanes 64 r00_st008 = r00_st009 := by decide +kernel
theorem r00_s009 : run 26 lanes 64 r00_st009 = r00_st010 := by decide +kernel
theorem r00_s010 : run 26 lanes 64 r00_st010 = r00_st011 := by decide +kernel
theorem r00_s011 : run 26 lanes 64 r00_st011 = r00_st012 := by decide +kernel
theorem r00_s012 : run 26 lanes 64 r00_st012 = r00_st013 := by decide +kernel
theorem r00_s013 : run 26 lanes 64 r00_st013 = r00_st014 := by decide +kernel
theorem r00_s014 : run 26 lanes 64 r00_st014 = r00_st015 := by decide +kernel
theorem r00_s015 : run 26 lanes 64 r00_st015 = r00_st016 := by decide +kernel
theorem r00_s016 : run 26 lanes 64 r00_st016 = r00_st017 := by decide +kernel
theorem r00_s017 : run 26 lanes 64 r00_st017 = r00_st018 := by decide +kernel
theorem r00_s018 : run 26 lanes 64 r00_st018 = r00_st019 := by decide +kernel
theorem r00_s019 : run 26 lanes 64 r00_st019 = r00_st020 := by decide +kernel
theorem r00_s020 : run 26 lanes 64 r00_st020 = r00_st021 := by decide +kernel
theorem r00_s021 : run 26 lanes 64 r00_st021 = r00_st022 := by decide +kernel
theorem r00_s022 : run 26 lanes 64 r00_st022 = r00_st023 := by decide +kernel
theorem r00_s023 : run 26 lanes 64 r00_st023 = r00_st024 := by decide +kernel
theorem r00_s024 : run 26 lanes 64 r00_st024 = r00_st025 := by decide +kernel
theorem r00_s025 : run 26 lanes 64 r00_st025 = r00_st026 := by decide +kernel
theorem r00_s026 : run 26 lanes 64 r00_st026 = r00_st027 := by decide +kernel
theorem r00_s027 : run 26 lanes 64 r00_st027 = r00_st028 := by decide +kernel
theorem r00_s028 : run 26 lanes 64 r00_st028 = r00_st029 := by decide +kernel
theorem r00_s029 : run 26 lanes 64 r00_st029 = r00_st030 := by decide +kernel
theorem r00_s030 : run 26 lanes 64 r00_st030 = r00_st031 := by decide +kernel
theorem r00_s031 : run 26 lanes 64 r00_st031 = r00_st032 := by decide +kernel
theorem r00_s032 : run 26 lanes 64 r00_st032 = r00_st033 := by decide +kernel
theorem r00_s033 : run 26 lanes 64 r00_st033 = r00_st034 := by decide +kernel
theorem r00_s034 : run 26 lanes 64 r00_st034 = r00_st035 := by decide +kernel
theorem r00_s035 : run 26 lanes 64 r00_st035 = r00_st036 := by decide +kernel
theorem r00_s036 : run 26 lanes 64 r00_st036 = r00_st037 := by decide +kernel
theorem r00_s037 : run 26 lanes 64 r00_st037 = r00_st038 := by decide +kernel
theorem r00_s038 : run 26 lanes 64 r00_st038 = r00_st039 := by decide +kernel
theorem r00_s039 : run 26 lanes 64 r00_st039 = r00_st040 := by decide +kernel
theorem r00_s040 : run 26 lanes 64 r00_st040 = r00_st041 := by decide +kernel
theorem r00_s041 : run 26 lanes 64 r00_st041 = r00_st042 := by decide +kernel
theorem r00_s042 : run 26 lanes 64 r00_st042 = r00_st043 := by decide +kernel
theorem r00_s043 : run 26 lanes 64 r00_st043 = r00_st044 := by decide +kernel
theorem r00_s044 : run 26 lanes 64 r00_st044 = r00_st045 := by decide +kernel
theorem r00_s045 : run 26 lanes 64 r00_st045 = r00_st046 := by decide +kernel
theorem r00_s046 : run 26 lanes 64 r00_st046 = r00_st047 := by decide +kernel
theorem r00_s047 : run 26 lanes 64 r00_st047 = r00_st048 := by decide +kernel
theorem r00_s048 : run 26 lanes 64 r00_st048 = r00_st049 := by decide +kernel
theorem r00_s049 : run 26 lanes 64 r00_st049 = r00_st050 := by decide +kernel
theorem r00_s050 : run 26 lanes 64 r00_st050 = r00_st051 := by decide +kernel
theorem r00_s051 : run 26 lanes 64 r00_st051 = r00_st052 := by decide +kernel
theorem r00_s052 : run 26 lanes 64 r00_st052 = r00_st053 := by decide +kernel
theorem r00_s053 : run 26 lanes 64 r00_st053 = r00_st054 := by decide +kernel
theorem r00_s054 : run 26 lanes 64 r00_st054 = r00_st055 := by decide +kernel
theorem r00_s055 : run 26 lanes 64 r00_st055 = r00_st056 := by decide +kernel
theorem r00_s056 : run 26 lanes 64 r00_st056 = r00_st057 := by decide +kernel
theorem r00_s057 : run 26 lanes 64 r00_st057 = r00_st058 := by decide +kernel
theorem r00_s058 : run 26 lanes 64 r00_st058 = r00_st059 := by decide +kernel
theorem r00_s059 : run 26 lanes 64 r00_st059 = r00_st060 := by decide +kernel
theorem r00_s060 : run 26 lanes 64 r00_st060 = r00_st061 := by decide +kernel
theorem r00_s061 : run 26 lanes 64 r00_st061 = r00_st062 := by decide +kernel
theorem r00_s062 : run 26 lanes 64 r00_st062 = r00_st063 := by decide +kernel
theorem r00_s063 : run 26 lanes 64 r00_st063 = r00_st064 := by decide +kernel
theorem r00_s064 : run 26 lanes 64 r00_st064 = r00_st065 := by decide +kernel
theorem r00_s065 : run 26 lanes 64 r00_st065 = r00_st066 := by decide +kernel
theorem r00_s066 : run 26 lanes 64 r00_st066 = r00_st067 := by decide +kernel
theorem r00_s067 : run 26 lanes 64 r00_st067 = r00_st068 := by decide +kernel
theorem r00_s068 : run 26 lanes 64 r00_st068 = r00_st069 := by decide +kernel
theorem r00_s069 : run 26 lanes 64 r00_st069 = r00_st070 := by decide +kernel
theorem r00_s070 : run 26 lanes 64 r00_st070 = r00_st071 := by decide +kernel
theorem r00_s071 : run 26 lanes 64 r00_st071 = r00_st072 := by decide +kernel
theorem r00_s072 : run 26 lanes 64 r00_st072 = r00_st073 := by decide +kernel
theorem r00_s073 : run 26 lanes 64 r00_st073 = r00_st074 := by decide +kernel
theorem r00_s074 : run 26 lanes 64 r00_st074 = r00_st075 := by decide +kernel
theorem r00_s075 : run 26 lanes 64 r00_st075 = r00_st076 := by decide +kernel
theorem r00_s076 : run 26 lanes 64 r00_st076 = r00_st077 := by decide +kernel
theorem r00_s077 : run 26 lanes 64 r00_st077 = r00_st078 := by decide +kernel
theorem r00_s078 : run 26 lanes 64 r00_st078 = r00_st079 := by decide +kernel
theorem r00_s079 : run 26 lanes 64 r00_st079 = r00_st080 := by decide +kernel
theorem r00_s080 : run 26 lanes 64 r00_st080 = r00_st081 := by decide +kernel
theorem r00_s081 : run 26 lanes 64 r00_st081 = r00_st082 := by decide +kernel
theorem r00_s082 : run 26 lanes 64 r00_st082 = r00_st083 := by decide +kernel
theorem r00_s083 : run 26 lanes 64 r00_st083 = r00_st084 := by decide +kernel
theorem r00_s084 : run 26 lanes 64 r00_st084 = r00_st085 := by decide +kernel
theorem r00_s085 : run 26 lanes 64 r00_st085 = r00_st086 := by decide +kernel
theorem r00_s086 : run 26 lanes 64 r00_st086 = r00_st087 := by decide +kernel
theorem r00_s087 : run 26 lanes 64 r00_st087 = r00_st088 := by decide +kernel
theorem r00_s088 : run 26 lanes 64 r00_st088 = r00_st089 := by decide +kernel
theorem r00_s089 : run 26 lanes 64 r00_st089 = r00_st090 := by decide +kernel
theorem r00_s090 : run 26 lanes 64 r00_st090 = r00_st091 := by decide +kernel
theorem r00_s091 : run 26 lanes 64 r00_st091 = r00_st092 := by decide +kernel
theorem r00_s092 : run 26 lanes 64 r00_st092 = r00_st093 := by decide +kernel
theorem r00_s093 : run 26 lanes 64 r00_st093 = r00_st094 := by decide +kernel
theorem r00_s094 : run 26 lanes 64 r00_st094 = r00_st095 := by decide +kernel
theorem r00_s095 : run 26 lanes 64 r00_st095 = r00_st096 := by decide +kernel
theorem r00_s096 : run 26 lanes 64 r00_st096 = r00_st097 := by decide +kernel
theorem r00_s097 : run 26 lanes 64 r00_st097 = r00_st098 := by decide +kernel
theorem r00_s098 : run 26 lanes 41 r00_st098 = state001 := by decide +kernel
theorem r00_c0_000 : run 26 lanes 128 state000 = r00_st002 := run_chain r00_s000 r00_s001
theorem r00_c0_001 : run 26 lanes 128 r00_st002 = r00_st004 := run_chain r00_s002 r00_s003
theorem r00_c0_002 : run 26 lanes 128 r00_st004 = r00_st006 := run_chain r00_s004 r00_s005
theorem r00_c0_003 : run 26 lanes 128 r00_st006 = r00_st008 := run_chain r00_s006 r00_s007
theorem r00_c0_004 : run 26 lanes 128 r00_st008 = r00_st010 := run_chain r00_s008 r00_s009
theorem r00_c0_005 : run 26 lanes 128 r00_st010 = r00_st012 := run_chain r00_s010 r00_s011
theorem r00_c0_006 : run 26 lanes 128 r00_st012 = r00_st014 := run_chain r00_s012 r00_s013
theorem r00_c0_007 : run 26 lanes 128 r00_st014 = r00_st016 := run_chain r00_s014 r00_s015
theorem r00_c0_008 : run 26 lanes 128 r00_st016 = r00_st018 := run_chain r00_s016 r00_s017
theorem r00_c0_009 : run 26 lanes 128 r00_st018 = r00_st020 := run_chain r00_s018 r00_s019
theorem r00_c0_010 : run 26 lanes 128 r00_st020 = r00_st022 := run_chain r00_s020 r00_s021
theorem r00_c0_011 : run 26 lanes 128 r00_st022 = r00_st024 := run_chain r00_s022 r00_s023
theorem r00_c0_012 : run 26 lanes 128 r00_st024 = r00_st026 := run_chain r00_s024 r00_s025
theorem r00_c0_013 : run 26 lanes 128 r00_st026 = r00_st028 := run_chain r00_s026 r00_s027
theorem r00_c0_014 : run 26 lanes 128 r00_st028 = r00_st030 := run_chain r00_s028 r00_s029
theorem r00_c0_015 : run 26 lanes 128 r00_st030 = r00_st032 := run_chain r00_s030 r00_s031
theorem r00_c0_016 : run 26 lanes 128 r00_st032 = r00_st034 := run_chain r00_s032 r00_s033
theorem r00_c0_017 : run 26 lanes 128 r00_st034 = r00_st036 := run_chain r00_s034 r00_s035
theorem r00_c0_018 : run 26 lanes 128 r00_st036 = r00_st038 := run_chain r00_s036 r00_s037
theorem r00_c0_019 : run 26 lanes 128 r00_st038 = r00_st040 := run_chain r00_s038 r00_s039
theorem r00_c0_020 : run 26 lanes 128 r00_st040 = r00_st042 := run_chain r00_s040 r00_s041
theorem r00_c0_021 : run 26 lanes 128 r00_st042 = r00_st044 := run_chain r00_s042 r00_s043
theorem r00_c0_022 : run 26 lanes 128 r00_st044 = r00_st046 := run_chain r00_s044 r00_s045
theorem r00_c0_023 : run 26 lanes 128 r00_st046 = r00_st048 := run_chain r00_s046 r00_s047
theorem r00_c0_024 : run 26 lanes 128 r00_st048 = r00_st050 := run_chain r00_s048 r00_s049
theorem r00_c0_025 : run 26 lanes 128 r00_st050 = r00_st052 := run_chain r00_s050 r00_s051
theorem r00_c0_026 : run 26 lanes 128 r00_st052 = r00_st054 := run_chain r00_s052 r00_s053
theorem r00_c0_027 : run 26 lanes 128 r00_st054 = r00_st056 := run_chain r00_s054 r00_s055
theorem r00_c0_028 : run 26 lanes 128 r00_st056 = r00_st058 := run_chain r00_s056 r00_s057
theorem r00_c0_029 : run 26 lanes 128 r00_st058 = r00_st060 := run_chain r00_s058 r00_s059
theorem r00_c0_030 : run 26 lanes 128 r00_st060 = r00_st062 := run_chain r00_s060 r00_s061
theorem r00_c0_031 : run 26 lanes 128 r00_st062 = r00_st064 := run_chain r00_s062 r00_s063
theorem r00_c0_032 : run 26 lanes 128 r00_st064 = r00_st066 := run_chain r00_s064 r00_s065
theorem r00_c0_033 : run 26 lanes 128 r00_st066 = r00_st068 := run_chain r00_s066 r00_s067
theorem r00_c0_034 : run 26 lanes 128 r00_st068 = r00_st070 := run_chain r00_s068 r00_s069
theorem r00_c0_035 : run 26 lanes 128 r00_st070 = r00_st072 := run_chain r00_s070 r00_s071
theorem r00_c0_036 : run 26 lanes 128 r00_st072 = r00_st074 := run_chain r00_s072 r00_s073
theorem r00_c0_037 : run 26 lanes 128 r00_st074 = r00_st076 := run_chain r00_s074 r00_s075
theorem r00_c0_038 : run 26 lanes 128 r00_st076 = r00_st078 := run_chain r00_s076 r00_s077
theorem r00_c0_039 : run 26 lanes 128 r00_st078 = r00_st080 := run_chain r00_s078 r00_s079
theorem r00_c0_040 : run 26 lanes 128 r00_st080 = r00_st082 := run_chain r00_s080 r00_s081
theorem r00_c0_041 : run 26 lanes 128 r00_st082 = r00_st084 := run_chain r00_s082 r00_s083
theorem r00_c0_042 : run 26 lanes 128 r00_st084 = r00_st086 := run_chain r00_s084 r00_s085
theorem r00_c0_043 : run 26 lanes 128 r00_st086 = r00_st088 := run_chain r00_s086 r00_s087
theorem r00_c0_044 : run 26 lanes 128 r00_st088 = r00_st090 := run_chain r00_s088 r00_s089
theorem r00_c0_045 : run 26 lanes 128 r00_st090 = r00_st092 := run_chain r00_s090 r00_s091
theorem r00_c0_046 : run 26 lanes 128 r00_st092 = r00_st094 := run_chain r00_s092 r00_s093
theorem r00_c0_047 : run 26 lanes 128 r00_st094 = r00_st096 := run_chain r00_s094 r00_s095
theorem r00_c0_048 : run 26 lanes 128 r00_st096 = r00_st098 := run_chain r00_s096 r00_s097
theorem r00_c1_000 : run 26 lanes 256 state000 = r00_st004 := run_chain r00_c0_000 r00_c0_001
theorem r00_c1_001 : run 26 lanes 256 r00_st004 = r00_st008 := run_chain r00_c0_002 r00_c0_003
theorem r00_c1_002 : run 26 lanes 256 r00_st008 = r00_st012 := run_chain r00_c0_004 r00_c0_005
theorem r00_c1_003 : run 26 lanes 256 r00_st012 = r00_st016 := run_chain r00_c0_006 r00_c0_007
theorem r00_c1_004 : run 26 lanes 256 r00_st016 = r00_st020 := run_chain r00_c0_008 r00_c0_009
theorem r00_c1_005 : run 26 lanes 256 r00_st020 = r00_st024 := run_chain r00_c0_010 r00_c0_011
theorem r00_c1_006 : run 26 lanes 256 r00_st024 = r00_st028 := run_chain r00_c0_012 r00_c0_013
theorem r00_c1_007 : run 26 lanes 256 r00_st028 = r00_st032 := run_chain r00_c0_014 r00_c0_015
theorem r00_c1_008 : run 26 lanes 256 r00_st032 = r00_st036 := run_chain r00_c0_016 r00_c0_017
theorem r00_c1_009 : run 26 lanes 256 r00_st036 = r00_st040 := run_chain r00_c0_018 r00_c0_019
theorem r00_c1_010 : run 26 lanes 256 r00_st040 = r00_st044 := run_chain r00_c0_020 r00_c0_021
theorem r00_c1_011 : run 26 lanes 256 r00_st044 = r00_st048 := run_chain r00_c0_022 r00_c0_023
theorem r00_c1_012 : run 26 lanes 256 r00_st048 = r00_st052 := run_chain r00_c0_024 r00_c0_025
theorem r00_c1_013 : run 26 lanes 256 r00_st052 = r00_st056 := run_chain r00_c0_026 r00_c0_027
theorem r00_c1_014 : run 26 lanes 256 r00_st056 = r00_st060 := run_chain r00_c0_028 r00_c0_029
theorem r00_c1_015 : run 26 lanes 256 r00_st060 = r00_st064 := run_chain r00_c0_030 r00_c0_031
theorem r00_c1_016 : run 26 lanes 256 r00_st064 = r00_st068 := run_chain r00_c0_032 r00_c0_033
theorem r00_c1_017 : run 26 lanes 256 r00_st068 = r00_st072 := run_chain r00_c0_034 r00_c0_035
theorem r00_c1_018 : run 26 lanes 256 r00_st072 = r00_st076 := run_chain r00_c0_036 r00_c0_037
theorem r00_c1_019 : run 26 lanes 256 r00_st076 = r00_st080 := run_chain r00_c0_038 r00_c0_039
theorem r00_c1_020 : run 26 lanes 256 r00_st080 = r00_st084 := run_chain r00_c0_040 r00_c0_041
theorem r00_c1_021 : run 26 lanes 256 r00_st084 = r00_st088 := run_chain r00_c0_042 r00_c0_043
theorem r00_c1_022 : run 26 lanes 256 r00_st088 = r00_st092 := run_chain r00_c0_044 r00_c0_045
theorem r00_c1_023 : run 26 lanes 256 r00_st092 = r00_st096 := run_chain r00_c0_046 r00_c0_047
theorem r00_c1_024 : run 26 lanes 169 r00_st096 = state001 := run_chain r00_c0_048 r00_s098
theorem r00_c2_000 : run 26 lanes 512 state000 = r00_st008 := run_chain r00_c1_000 r00_c1_001
theorem r00_c2_001 : run 26 lanes 512 r00_st008 = r00_st016 := run_chain r00_c1_002 r00_c1_003
theorem r00_c2_002 : run 26 lanes 512 r00_st016 = r00_st024 := run_chain r00_c1_004 r00_c1_005
theorem r00_c2_003 : run 26 lanes 512 r00_st024 = r00_st032 := run_chain r00_c1_006 r00_c1_007
theorem r00_c2_004 : run 26 lanes 512 r00_st032 = r00_st040 := run_chain r00_c1_008 r00_c1_009
theorem r00_c2_005 : run 26 lanes 512 r00_st040 = r00_st048 := run_chain r00_c1_010 r00_c1_011
theorem r00_c2_006 : run 26 lanes 512 r00_st048 = r00_st056 := run_chain r00_c1_012 r00_c1_013
theorem r00_c2_007 : run 26 lanes 512 r00_st056 = r00_st064 := run_chain r00_c1_014 r00_c1_015
theorem r00_c2_008 : run 26 lanes 512 r00_st064 = r00_st072 := run_chain r00_c1_016 r00_c1_017
theorem r00_c2_009 : run 26 lanes 512 r00_st072 = r00_st080 := run_chain r00_c1_018 r00_c1_019
theorem r00_c2_010 : run 26 lanes 512 r00_st080 = r00_st088 := run_chain r00_c1_020 r00_c1_021
theorem r00_c2_011 : run 26 lanes 512 r00_st088 = r00_st096 := run_chain r00_c1_022 r00_c1_023
theorem r00_c3_000 : run 26 lanes 1024 state000 = r00_st016 := run_chain r00_c2_000 r00_c2_001
theorem r00_c3_001 : run 26 lanes 1024 r00_st016 = r00_st032 := run_chain r00_c2_002 r00_c2_003
theorem r00_c3_002 : run 26 lanes 1024 r00_st032 = r00_st048 := run_chain r00_c2_004 r00_c2_005
theorem r00_c3_003 : run 26 lanes 1024 r00_st048 = r00_st064 := run_chain r00_c2_006 r00_c2_007
theorem r00_c3_004 : run 26 lanes 1024 r00_st064 = r00_st080 := run_chain r00_c2_008 r00_c2_009
theorem r00_c3_005 : run 26 lanes 1024 r00_st080 = r00_st096 := run_chain r00_c2_010 r00_c2_011
theorem r00_c4_000 : run 26 lanes 2048 state000 = r00_st032 := run_chain r00_c3_000 r00_c3_001
theorem r00_c4_001 : run 26 lanes 2048 r00_st032 = r00_st064 := run_chain r00_c3_002 r00_c3_003
theorem r00_c4_002 : run 26 lanes 2048 r00_st064 = r00_st096 := run_chain r00_c3_004 r00_c3_005
theorem r00_c5_000 : run 26 lanes 4096 state000 = r00_st064 := run_chain r00_c4_000 r00_c4_001
theorem r00_c5_001 : run 26 lanes 2217 r00_st064 = state001 := run_chain r00_c4_002 r00_c1_024
theorem r00_c6_000 : run 26 lanes 6313 state000 = state001 := run_chain r00_c5_000 r00_c5_001

theorem run_00 : run 26 lanes 6313 state000 = state001 := r00_c6_000

def r01_st001 : LaneState := ⟨17194582, 1, [0x55555555, 0x33333333, 0xdddddddd, 0x2d2d2d2d, 0x37373737, 0xbb44bb44, 0xce0dce0d, 0x1e73e18c, 0xcae19f6a, 0x98fc0890]⟩
def r01_st002 : LaneState := ⟨20652630, 1, [0xaaaaaaaa, 0xcccccccc, 0x77777777, 0x5a5a5a5a, 0x9b9b9b9b, 0x42bd42bd, 0x23df23df, 0xb9c4463b, 0x8cc5f739, 0x10967f05]⟩
def r01_st003 : LaneState := ⟨33039958, 1, [0x55555555, 0x66666666, 0x22222222, 0xc3c3c3c3, 0xe5e5e5e5, 0x807f807f, 0xe278e278, 0xff5c00a3, 0xb8c81ade, 0x8f610fe2]⟩
def r01_st004 : LaneState := ⟨21350998, 1, [0xaaaaaaaa, 0x66666666, 0x44444444, 0x2d2d2d2d, 0x5d5d5d5d, 0x7a857a85, 0x541c541c, 0x3a6ac595, 0xf48cc695, 0x6e11a69]⟩
def r01_st005 : LaneState := ⟨27319894, 1, [0x55555555, 0xcccccccc, 0xdddddddd, 0xb4b4b4b4, 0x8a8a8a8a, 0x8c738c73, 0x6d166d16, 0x630e9cf1, 0x4611fa2f, 0x5c1fb268]⟩
def r01_st006 : LaneState := ⟨5218902, 1, [0xaaaaaaaa, 0x99999999, 0x11111111, 0x5a5a5a5a, 0xb6b6b6b6, 0x4cb34cb3, 0x7f107f10, 0xbe3a41c5, 0x9a3ca3c5, 0xa7ccd6af]⟩
def r01_st007 : LaneState := ⟨56600150, 1, [0xaaaaaaaa, 0x33333333, 0x88888888, 0xc3c3c3c3, 0x70707070, 0x78877887, 0xf743f743, 0x785987a6, 0xb6c88b9, 0x470d9994]⟩
def r01_st008 : LaneState := ⟨16337494, 1, [0x55555555, 0x99999999, 0xeeeeeeee, 0x69696969, 0x6b6b6b6b, 0xf30cf30c, 0xdd78dd78, 0x3512caed, 0x99e7c868, 0x26dd47d6]⟩
def r01_st009 : LaneState := ⟨54287958, 1, [0xaaaaaaaa, 0x33333333, 0xbbbbbbbb, 0x2d2d2d2d, 0x9e9e9e9e, 0x30cf30cf, 0xc1dac1da, 0xc3933c6c, 0x9018c8ad, 0x6e34015e]⟩
def r01_st010 : LaneState := ⟨5579350, 1, [0x55555555, 0x99999999, 0xeeeeeeee, 0xf0f0f0f, 0xb5b5b5b5, 0x41be41be, 0xbc6dbc6d, 0xdf3820c7, 0xa55351d0, 0x894b787d]⟩
def r01_st011 : LaneState := ⟨37889622, 1, [0x55555555, 0xcccccccc, 0xdddddddd, 0x69696969, 0x54545454, 0xf10ef10e, 0x94619461, 0xb95546aa, 0xfd7f34fd, 0xfff8c397]⟩
def r01_st012 : LaneState := ⟨56347222, 1, [0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xd6d6d6d6, 0xe619e619, 0x2a252a25, 0xc0d13f2e, 0xc64d5ff, 0x2be49b58]⟩
def r01_st013 : LaneState := ⟨18800214, 1, [0x55555555, 0x66666666, 0xdddddddd, 0x78787878, 0x19191919, 0x837c837c, 0xedbeedbe, 0xfbf80407, 0x7ae4cbbd, 0x4dc11266]⟩
def r01_st014 : LaneState := ⟨42836566, 1, [0xaaaaaaaa, 0xcccccccc, 0x44444444, 0xf0f0f0f, 0xc1c1c1c1, 0x6c936c93, 0x37f737f7, 0x1b4fe4b, 0xc0f09d80, 0x190354ab]⟩
def r01_st015 : LaneState := ⟨60139094, 1, [0x55555555, 0x99999999, 0x11111111, 0x69696969, 0xfbfbfbfb, 0xd728d728, 0x215f215f, 0x4b21b4de, 0xbedf488f, 0xac0a2d9b]⟩
def r01_st016 : LaneState := ⟨49760854, 1, [0x55555555, 0xcccccccc, 0x44444444, 0xf0f0f0f0, 0xdcdcdcdc, 0x906f906f, 0xd5a2d5a2, 0x7a3585ca, 0x575e47bb, 0x62dd7fbf]⟩
def r01_st017 : LaneState := ⟨37903958, 1, [0xaaaaaaaa, 0xcccccccc, 0x44444444, 0x78787878, 0x51515151, 0x2bd42bd4, 0x3f743f74, 0x889a7765, 0xbf7baa8a, 0x5b77479e]⟩
def r01_st018 : LaneState := ⟨27730518, 1, [0xaaaaaaaa, 0x33333333, 0x44444444, 0x1e1e1e1e, 0x6e6e6e6e, 0xe01fe01f, 0x1dc01dc, 0x397bc684, 0xaccbe018, 0x4e6f4a3e]⟩
def r01_st019 : LaneState := ⟨9184854, 1, [0xaaaaaaaa, 0xcccccccc, 0x77777777, 0xf0f0f0f0, 0xa2a2a2a2, 0xb649b649, 0xd380d38, 0xc9d0362f, 0x9cc24da1, 0x4b4b7d2b]⟩
def r01_st020 : LaneState := ⟨20040278, 1, [0xaaaaaaaa, 0x33333333, 0x11111111, 0x2d2d2d2d, 0x4040404, 0x96699669, 0xc600c600, 0x1f48e0b7, 0xe310ebd7, 0xf0bf7e06]⟩
def r01_st021 : LaneState := ⟨5037654, 1, [0xaaaaaaaa, 0xcccccccc, 0x44444444, 0xf0f0f0f, 0x83838383, 0x47b847b8, 0x7d357d35, 0x6b5194ae, 0x4446a111, 0xf1f4e9af]⟩
def r01_st022 : LaneState := ⟨48996950, 1, [0x55555555, 0x33333333, 0x22222222, 0xa5a5a5a5, 0xeaeaeaea, 0x946b946b, 0xba2cba2c, 0x1bf7e408, 0x15452271, 0xcd01b92]⟩
def r01_st023 : LaneState := ⟨14919254, 1, [0xaaaaaaaa, 0xcccccccc, 0xbbbbbbbb, 0xb4b4b4b4, 0x4c4c4c4c, 0x9e619e61, 0x91709170, 0xc61f39e, 0x73d1698c, 0x2fc0740b]⟩
def r01_st024 : LaneState := ⟨13978198, 1, [0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0x3c3c3c3c, 0x3b3b3b3b, 0xed12ed12, 0xec3eec3e, 0x459dba62, 0x3eff070c, 0xb3200c32]⟩
def r01_st025 : LaneState := ⟨15228502, 1, [0xaaaaaaaa, 0xcccccccc, 0x22222222, 0x4b4b4b4b, 0x45454545, 0xd02fd02f, 0xee50ee5, 0xd63829c7, 0xc07a2c17, 0x8731022b]⟩
def r01_st026 : LaneState := ⟨16327254, 1, [0x55555555, 0x66666666, 0xbbbbbbbb, 0x87878787, 0xe0e0e0e0, 0x3dc23dc2, 0x85868586, 0x93cf6c3, 0xdff4b54, 0xf72d7761]⟩
def r01_st027 : LaneState := ⟨64366166, 1, [0x55555555, 0x33333333, 0x88888888, 0x78787878, 0xf7f7f7f7, 0x9f609f6, 0xe586e586, 0xf40d0bf2, 0xa65ce07c, 0xb62c6227]⟩
def r01_st028 : LaneState := ⟨11520598, 1, [0x55555555, 0x99999999, 0x44444444, 0x4b4b4b4b, 0x38383838, 0x7f807f80, 0xb00db00d, 0x5f79a086, 0xefadfb64, 0xdbd054c2]⟩
def r01_st029 : LaneState := ⟨23256662, 1, [0x55555555, 0xcccccccc, 0x22222222, 0xf0f0f0f, 0xdfdfdfdf, 0x649b649b, 0x8a988a98, 0x9cec6313, 0x2f9dd51f, 0xc092ab11]⟩

theorem r01_s000 : run 26 lanes 64 state001 = r01_st001 := by decide +kernel
theorem r01_s001 : run 26 lanes 64 r01_st001 = r01_st002 := by decide +kernel
theorem r01_s002 : run 26 lanes 64 r01_st002 = r01_st003 := by decide +kernel
theorem r01_s003 : run 26 lanes 64 r01_st003 = r01_st004 := by decide +kernel
theorem r01_s004 : run 26 lanes 64 r01_st004 = r01_st005 := by decide +kernel
theorem r01_s005 : run 26 lanes 64 r01_st005 = r01_st006 := by decide +kernel
theorem r01_s006 : run 26 lanes 64 r01_st006 = r01_st007 := by decide +kernel
theorem r01_s007 : run 26 lanes 64 r01_st007 = r01_st008 := by decide +kernel
theorem r01_s008 : run 26 lanes 64 r01_st008 = r01_st009 := by decide +kernel
theorem r01_s009 : run 26 lanes 64 r01_st009 = r01_st010 := by decide +kernel
theorem r01_s010 : run 26 lanes 64 r01_st010 = r01_st011 := by decide +kernel
theorem r01_s011 : run 26 lanes 64 r01_st011 = r01_st012 := by decide +kernel
theorem r01_s012 : run 26 lanes 64 r01_st012 = r01_st013 := by decide +kernel
theorem r01_s013 : run 26 lanes 64 r01_st013 = r01_st014 := by decide +kernel
theorem r01_s014 : run 26 lanes 64 r01_st014 = r01_st015 := by decide +kernel
theorem r01_s015 : run 26 lanes 64 r01_st015 = r01_st016 := by decide +kernel
theorem r01_s016 : run 26 lanes 64 r01_st016 = r01_st017 := by decide +kernel
theorem r01_s017 : run 26 lanes 64 r01_st017 = r01_st018 := by decide +kernel
theorem r01_s018 : run 26 lanes 64 r01_st018 = r01_st019 := by decide +kernel
theorem r01_s019 : run 26 lanes 64 r01_st019 = r01_st020 := by decide +kernel
theorem r01_s020 : run 26 lanes 64 r01_st020 = r01_st021 := by decide +kernel
theorem r01_s021 : run 26 lanes 64 r01_st021 = r01_st022 := by decide +kernel
theorem r01_s022 : run 26 lanes 64 r01_st022 = r01_st023 := by decide +kernel
theorem r01_s023 : run 26 lanes 64 r01_st023 = r01_st024 := by decide +kernel
theorem r01_s024 : run 26 lanes 64 r01_st024 = r01_st025 := by decide +kernel
theorem r01_s025 : run 26 lanes 64 r01_st025 = r01_st026 := by decide +kernel
theorem r01_s026 : run 26 lanes 64 r01_st026 = r01_st027 := by decide +kernel
theorem r01_s027 : run 26 lanes 64 r01_st027 = r01_st028 := by decide +kernel
theorem r01_s028 : run 26 lanes 64 r01_st028 = r01_st029 := by decide +kernel
theorem r01_s029 : run 26 lanes 23 r01_st029 = state002 := by decide +kernel
theorem r01_c0_000 : run 26 lanes 128 state001 = r01_st002 := run_chain r01_s000 r01_s001
theorem r01_c0_001 : run 26 lanes 128 r01_st002 = r01_st004 := run_chain r01_s002 r01_s003
theorem r01_c0_002 : run 26 lanes 128 r01_st004 = r01_st006 := run_chain r01_s004 r01_s005
theorem r01_c0_003 : run 26 lanes 128 r01_st006 = r01_st008 := run_chain r01_s006 r01_s007
theorem r01_c0_004 : run 26 lanes 128 r01_st008 = r01_st010 := run_chain r01_s008 r01_s009
theorem r01_c0_005 : run 26 lanes 128 r01_st010 = r01_st012 := run_chain r01_s010 r01_s011
theorem r01_c0_006 : run 26 lanes 128 r01_st012 = r01_st014 := run_chain r01_s012 r01_s013
theorem r01_c0_007 : run 26 lanes 128 r01_st014 = r01_st016 := run_chain r01_s014 r01_s015
theorem r01_c0_008 : run 26 lanes 128 r01_st016 = r01_st018 := run_chain r01_s016 r01_s017
theorem r01_c0_009 : run 26 lanes 128 r01_st018 = r01_st020 := run_chain r01_s018 r01_s019
theorem r01_c0_010 : run 26 lanes 128 r01_st020 = r01_st022 := run_chain r01_s020 r01_s021
theorem r01_c0_011 : run 26 lanes 128 r01_st022 = r01_st024 := run_chain r01_s022 r01_s023
theorem r01_c0_012 : run 26 lanes 128 r01_st024 = r01_st026 := run_chain r01_s024 r01_s025
theorem r01_c0_013 : run 26 lanes 128 r01_st026 = r01_st028 := run_chain r01_s026 r01_s027
theorem r01_c0_014 : run 26 lanes 87 r01_st028 = state002 := run_chain r01_s028 r01_s029
theorem r01_c1_000 : run 26 lanes 256 state001 = r01_st004 := run_chain r01_c0_000 r01_c0_001
theorem r01_c1_001 : run 26 lanes 256 r01_st004 = r01_st008 := run_chain r01_c0_002 r01_c0_003
theorem r01_c1_002 : run 26 lanes 256 r01_st008 = r01_st012 := run_chain r01_c0_004 r01_c0_005
theorem r01_c1_003 : run 26 lanes 256 r01_st012 = r01_st016 := run_chain r01_c0_006 r01_c0_007
theorem r01_c1_004 : run 26 lanes 256 r01_st016 = r01_st020 := run_chain r01_c0_008 r01_c0_009
theorem r01_c1_005 : run 26 lanes 256 r01_st020 = r01_st024 := run_chain r01_c0_010 r01_c0_011
theorem r01_c1_006 : run 26 lanes 256 r01_st024 = r01_st028 := run_chain r01_c0_012 r01_c0_013
theorem r01_c2_000 : run 26 lanes 512 state001 = r01_st008 := run_chain r01_c1_000 r01_c1_001
theorem r01_c2_001 : run 26 lanes 512 r01_st008 = r01_st016 := run_chain r01_c1_002 r01_c1_003
theorem r01_c2_002 : run 26 lanes 512 r01_st016 = r01_st024 := run_chain r01_c1_004 r01_c1_005
theorem r01_c2_003 : run 26 lanes 343 r01_st024 = state002 := run_chain r01_c1_006 r01_c0_014
theorem r01_c3_000 : run 26 lanes 1024 state001 = r01_st016 := run_chain r01_c2_000 r01_c2_001
theorem r01_c3_001 : run 26 lanes 855 r01_st016 = state002 := run_chain r01_c2_002 r01_c2_003
theorem r01_c4_000 : run 26 lanes 1879 state001 = state002 := run_chain r01_c3_000 r01_c3_001

theorem run_01 : run 26 lanes 1879 state001 = state002 := r01_c4_000

theorem run_prefix : run 26 lanes 6313 state000 = state001 := run_00

theorem run_full : run 26 lanes 8192 state000 = state002 :=
  run_chain run_00 run_01

def prefixWord (j : Nat) : Nat := word 26 (project j state001)

theorem initial_words : (List.range 32).all (fun j =>
    word 26 (project j state000) == embedding j) = true := by decide +kernel

theorem endpoint_words : (List.range 32).all (fun j =>
    word 26 (project j state002) == embedding (nextIndex j)) = true := by decide +kernel

theorem initial_word (j : Nat) (hj : j < 32) : word 26 (project j state000) = embedding j :=
  Nat.beq_eq.mp (List.all_eq_true.mp initial_words j (List.mem_range.mpr hj))

theorem endpoint_word (j : Nat) (hj : j < 32) : word 26 (project j state002) = embedding (nextIndex j) :=
  Nat.beq_eq.mp (List.all_eq_true.mp endpoint_words j (List.mem_range.mpr hj))

theorem rare_table : (List.range 32).all (fun j =>
    sig 36 (8192*j+6313) (prefixWord j)) = true := by decide +kernel

theorem rare_table_sound (j : Nat) (hj : j < 32) :
    sig 36 (8192*j+6313) (prefixWord j) = true :=
  List.all_eq_true.mp rare_table j (List.mem_range.mpr hj)

theorem return_cycle : iter nextIndex 32 0 = 0 := by decide +kernel

theorem index_table : (List.range 32).all (fun j => iter nextIndex j 0 == j) = true := by decide +kernel

theorem iter_index (j : Nat) (hj : j < 32) : iter nextIndex j 0 = j :=
  Nat.beq_eq.mp (List.all_eq_true.mp index_table j (List.mem_range.mpr hj))

theorem lanes_bit (j : Nat) (hj : j < 32) : lanes.testBit j = true := by
  unfold lanes
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

theorem seg97_0 : seg 26 25 1 58411606 1 6313 0 97 0 = true := by decide +kernel
theorem seg97_1 : seg 26 25 1 97 0 1878 6314 8714155 0 = true := by decide +kernel

theorem cyc97_part1 : PathOK 26 25 1 0 (97, 0) (58411606, 1) 6313 :=
  seg_sound 26 25 1 58411606 1 6313 0 97 0 seg97_0

theorem cyc97_step6313 : orb 26 1 (58411606, 1) = (8714155, 0) := by decide +kernel

theorem cyc97_part2 : PathOK 26 25 1 6314 (8714155, 0) (97, 0) 1878 :=
  seg_sound 26 25 1 97 0 1878 6314 8714155 0 seg97_1

theorem cyc97_period : orb 26 8192 (97, 0) = (97, 0) := by
  rw [show (8192 : Nat) = 6313 + 1 + 1878 by decide +kernel, orb_add, orb_add,
      cyc97_part1.1, cyc97_step6313, cyc97_part2.1]

theorem cyc97_sig (r : Nat) (hr : r < 8192) (hodd : r % 2 = 1) (hne : r ≠ 6313) :
    sig 26 r (orb 26 r (97, 0)).1 = true := by
  by_cases hlt : r < 6313
  · have h := cyc97_part1.2 r hlt (by omega)
    rwa [Nat.zero_add] at h
  · have hgt : 6314 ≤ r := by omega
    obtain ⟨j, rfl⟩ : ∃ j, r = 6314 + j := ⟨r - 6314, by omega⟩
    have hj : j < 1878 := by omega
    have h := cyc97_part2.2 j hj hodd
    rwa [show 6314 + j = 6313 + 1 + j by omega, orb_add, orb_add,
         cyc97_part1.1, cyc97_step6313]

end Ruliology.CellularAutomata.Rule30Tail97Completion
