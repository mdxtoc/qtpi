# Experiments with QKD

## The scenario

Alice has a message *M* which she wants to send to Bob. She has a one-way quantum channel to him (at least she *thinks* it goes to him), and a [Wegman-Carter hash-tagged](#wegmancarter) two-way classical channel to him. She [calculates the number of qbits she will need](#enoughqbits), and sends them, one at a time and picking measurement basis and value for each at random, to Bob. Bob separately picks a random basis for each qbit, measures it in that basis, and records the results.

Then they do the QKD protocol dance: Alice sends the bases she chose to Bob through the classical channel and Bob sends the bases he chose back to Alice. They each select the subsequence of values for which they used the same basis, which will be about half of them, and throw the rest away. Now, supposing no interference with the qbits in transit, they share the same sequence of code bits. Bob picks a subsequence of his code bits, sends a bit-mask to Alice to characterise it, and the subsequence itself. Alice looks at the corresponding subsequence of her own code bits: if they have the same code bits then the two subsequences should be identical. If not, then some body or some thing has interfered with Alice's quantum transmissions.

If all seems ok Alice deletes Bob's checkbits from her code bits, takes a prefix of them to exclusive-or mask the message *M*, and sends it down the classical channel to Bob. Bob, having deleted his checkbits from his own code bits, takes a prefix of the same length, exclusive-or's it with the encrypted message, and he can see *M*. 

Before the protocol started Alice and Bob shared a secret: five short one-time hash keys, one for each of the five classical messages they exchange (bases A->B, bases B->A, bit-mask B->A, subsequence B->A, encrypted message A->B). Each classical message is tagged by a hash of the message and the corresponding hash key, and each tag is checked by the recipient, who uses the same hash function and knows the same hash key. If the tags aren't as expected then some body or some thing is spoofing messages on the classical channel. If all is ok when the protocol is over, Alice and Bob each take five new hash keys from the unused suffix of their code bits, and they are ready to run the protocol again. Crucially, the messages are sent in the clear, but the secret code bits are never disclosed, apart from the checkbit sequence sent by Bob.

In the simulation we want to log the intermediate stages of the protocol, especially if there is attempted interference, and we want to run multiple trials even if there is interference on the channels, so our Alice and Bob processes have a classical bit-list channel back to an experiment-controlling process. In reality Alice and/or Bob would fall silent if they detected interference; in the simulation they keep going to the end but Alice sends a blank message instead of an encrypted *M*. In reality Alice would be sure to pick enough qbits to ensure near certainty that she will have enough code bits to encrypt *M* and refresh the bit sequences; in the simulation she and Bob have a signalling channel and they can rerun the experiment if she doesn't have enough. 

In reality a repetition would be a security risk, because it would mean using hash keys for a second time, and multiple repetitions might give an eagle-eyed interceptor enough information to hack the classical channel. The frequency of repetition is a measure of Alice's success in calculating the number of qbits to use: see the [description of her calculation](#enoughqbits) for an analysis of repetition frequency and see the [no Eve trials](#noEve) for some experimental results.

<a name="enoughqbits"></a>
## Picking enough qbits

Suppose Alice's message *M* is *m* bits long, and that the Wegman-Carter one-time hash keys are each *w* bits long, so she needs at least

&emsp;&emsp;*k* = *m*+5*w*

secret code bits: *m* to encrypt *M* and send it to Bob, 5*w* to use for new hash keys. if *n* is the number of qbits she sends, then she can expect that about *n*/2 code bits will be agreed with Bob, who will then take a proportion of those -- in our simulation a quarter or *n*/8 -- for check bits. So *n*/2 - *n*/8 = 3*n*/8 has to be at least *k*. 

But she must also allow for statistical variation. She knows that the standard deviation &sigma; of the number of successes when choosing with probability *p* from a sequence length *n* is &radic;<span style="text-decoration:overline;">&nbsp;*np*(1-*p*)&nbsp;</span>. She wants the probability of choosing too few bits to be very small, so she must over-estimate. If she wants to be *s* &sigma;s away from trouble, well into the tail of the normal distribution, she can write some equations. 

First, Bob may choose more than *n*/8 bits: he chooses a bit with probability 1/4, so the worst-case pick that she has to allow for is more than *n*/8:

&emsp;&emsp;*b* = *n*/8 + *s*&radic;<span style="text-decoration:overline;">&nbsp;*n*/2(1/4)(3/4)&nbsp;</span>   

&emsp;&emsp;&emsp;&ensp;= *n*/8 + *s*&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>

If *s* is large enough Bob won't pick more than that many bits very often: [famously](https://en.wikipedia.org/wiki/68–95–99.7_rule) for *s*=5 the chances are 0.00003%, and they go down about three orders of magnitude for every increase in *s* after that. So Alice can give herself a comfortable allowance by choosing *s*=8 or *s*=10, or whatever she likes.

Alice and Bob will agree on the measurement basis for a qbit with probability 1/2. There will be statistical variation in the number of bits they agree on, and she must make sure that the number she needs is in the tail of the normal distribution, *s* &sigma;s away from the mean. So she can calculate 

&emsp;&emsp;*n*/2 &ge; *k* + *b* + *s*&radic;<span style="text-decoration:overline;">&nbsp;*n*(1/2)(1/2)&nbsp;</span>

&emsp;&emsp;&emsp;&ensp;= *k* + *b* + *s*/2&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>

&emsp;&emsp;&emsp;&ensp;= *k* + *n*/8 + *s*(&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>+1/2)&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span> 

Taking the inequality as an equality, this is a quadratic in &radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>:

&emsp;&emsp;3/8*n* - *s*(&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>+1/2)&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span> - *k* = 0

One of the solutions of this equation is negative, so we ignore it; the positive solution is 

&emsp;&emsp;&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span> = 4/3(*qs* + &radic;<span style="text-decoration:overline;">&nbsp;(*qs*)<sup>2</sup> + 3*k*/2&nbsp;</span>)
&emsp;where *q* = &radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>+1/2

Tricky in integer arithmetic ... so we approximate *q* = 806/1000 and do a lot of rounding up, which means Alice wastes some effort, but not too much. The [no Eve trials](#noEve) show how many bits she uses for various values of *k* and *s* and how it affects the repetition rate.

<a name="wegmancarter"></a>
## Wegman-carter hash-tagging

Not yet: watch this space.

<a name="noEve"></a>
## No Eve: just Alice and Bob

Trials to see if Alice picks enough qbits. Interference never detected because Eve isn't there: command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp SystemAB.qtp)

Note that in this simulation Bob doesn't know the length of *M*, still less the number of qbits Alice is going to send him. He reads qbits until he sees Alice's first message on the classical channel. Oh, the power of guarded sums!

### 0 Sigma  

        length of message? 100
        length of a hash key? 0
        number of sigmas? 0
        number of trials? 100
        
        289 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 20 repetition(s); average check bits 35 minimum check bits 22
        histogram of check-bit lengths
        [(22,1);(23,1);(24,3);(25,4);(27,3);(28,2);(29,4);(30,5);(31,4);(32,5);(33,2);(34,8);(35,6);(36,7);(37,8);(38,3);(39,7);(40,4
        );(41,8);(42,4);(43,1);(44,2);(46,1);(47,1);(48,3);(49,1);(51,1);(55,1)]

        real	0m21.096s
        user	0m0.709s
        sys	0m0.017s

 * About 20% repetition rate; less than expected but integer square root and rounding gives far too many bits with small number of &sigma;s; the analytical number of qbits is 266.

        length of message? 3
        length of a hash key? 0
        number of sigmas? 0
        number of trials? 100
        
        16 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 3 repetition(s); average check bits 1 minimum check bits 0
        histogram of check-bit lengths [(0,11);(1,29);(2,27);(3,25);(4,5);(5,3)]

        real	0m21.335s
        user	0m0.086s
        sys	0m0.005s
 
 * Even worse rounding: the analytical answer is 8. Oh well.
 
        length of message? 1000
        length of a hash key? 0
        number of sigmas? 0
        number of trials? 1000

        2704 qbits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 379 repetition(s); average check bits 336 minimum check bits 277
        histogram of check-bit lengths
        [(277,1);(290,1);(291,1);(294,2);(295,2);(297,1);(298,1);(299,2);(300,3);(301,5);(302,4);(303,3);(304,2);(305,6);(306,10);(
        307,3);(308,7);(309,5);(310,13);(311,7);(312,8);(313,13);(314,8);(315,9);(316,9);(317,13);(318,5);(319,17);(320,17);(321,13);
        (322,20);(323,15);(324,13);(325,16);(326,15);(327,20);(328,19);(329,23);(330,27);(331,27);(332,21);(333,29);(334,22);(335,15)
        ;(336,27);(337,25);(338,23);(339,28);(340,21);(341,22);(342,19);(343,21);(344,21);(345,25);(346,21);(347,20);(348,20);(349,26
        );(350,18);(351,12);(352,14);(353,12);(354,14);(355,17);(356,8);(357,8);(358,15);(359,6);(360,8);(361,11);(362,6);(363,5);(
        364,8);(365,4);(366,4);(367,4);(368,4);(369,7);(370,3);(371,2);(372,2);(373,3);(374,2);(376,1);(377,3);(378,1);(379,2);(381,1
        );(382,1);(383,1);(394,1)]

        real	1m40.728s
        user	1m19.496s
        sys	0m0.992s
        
 * With a longer message, and therefore many more qbits, it's possible to see that the calculation is working well enough. The repetition rate is 38%, and the number of qbits is somewhere between the 2666 that a 0-&sigma; experiment should use (when we should see error rates about 35%) and the 2780 that a 1-&sigma; should use (when we should see about 12%). Over-estimation by Alice, mostly caused by using integer square roots, is making her over-cautious. Never mind. So far as Alice is concerned, the calculation works.
 
### 1 Sigma

        length of message? 1000
        length of a hash key? 0
        number of sigmas? 1
        number of trials? 1000

        2809 qbits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 19 repetition(s); average check bits 351 minimum check bits 297
        histogram of check-bit lengths
        [(297,1);(302,1);(304,1);(305,1);(306,1);(307,1);(309,1);(311,4);(312,1);(313,2);(314,2);(315,1);(316,3);(317,2);(318,7);(319
        ,4);(320,7);(321,5);(322,6);(323,6);(324,7);(325,4);(326,5);(327,8);(328,11);(329,11);(330,6);(331,11);(332,14);(333,13);(334
        ,16);(335,16);(336,11);(337,20);(338,27);(339,20);(340,14);(341,13);(342,21);(343,19);(344,26);(345,21);(346,25);(347,23);(
        348,21);(349,29);(350,29);(351,17);(352,22);(353,27);(354,19);(355,19);(356,23);(357,21);(358,21);(359,14);(360,15);(361,17);
        (362,16);(363,12);(364,17);(365,24);(366,19);(367,16);(368,20);(369,12);(370,10);(371,9);(372,12);(373,8);(374,13);(375,8);(
        376,5);(377,9);(378,7);(379,10);(380,6);(381,6);(382,2);(383,7);(384,4);(385,9);(386,4);(387,2);(388,2);(389,1);(390,1);(392,
        3);(393,3);(395,1);(396,2);(397,2);(399,1);(400,1);(402,1);(405,1);(406,1)]

        real	1m26.289s
        user	1m1.882s
        sys	0m0.729s
  
  * Attempting to swamp the rounding errors by choosing a longer message.
  * Repetition rate about 0.2%, which is absurdly low. The analytical number of qbits is 2780, which explains the result. Alice is a little high but not so far out.
  
### 2 Sigma

        length of message? 1000
        length of a hash key? 0
        number of sigmas? 2
        number of trials? 100000

        3025 qbits per trial
        all done: 0 interfered with; 100000 exchanges succeeded; 0 failed; 0 repetition(s); average check bits 378 minimum check bits 302
        histogram of check-bit lengths
        [(302,1);(307,1);(308,1);(309,5);(310,3);(311,2);(312,1);(313,2);(314,5);(315,4);(316,2);(317,5);(318,7);(319,12);(320,12);(
        321,12);(322,12);(323,15);(324,25);(325,31);(326,26);(327,30);(328,34);(329,44);(330,63);(331,72);(332,81);(333,69);(334,90);
        (335,120);(336,152);(337,158);(338,166);(339,197);(340,247);(341,276);(342,311);(343,336);(344,409);(345,414);(346,472);(347,
        523);(348,582);(349,619);(350,641);(351,775);(352,781);(353,868);(354,894);(355,1010);(356,1020);(357,1143);(358,1226);(359,
        1276);(360,1371);(361,1453);(362,1483);(363,1479);(364,1705);(365,1650);(366,1766);(367,1838);(368,1885);(369,1922);(370,2012
        );(371,2061);(372,2100);(373,2064);(374,2116);(375,2173);(376,2224);(377,2254);(378,2156);(379,2168);(380,2221);(381,2221);(
        382,2014);(383,2155);(384,2069);(385,1962);(386,1951);(387,1921);(388,1752);(389,1863);(390,1768);(391,1702);(392,1573);(393,
        1567);(394,1537);(395,1496);(396,1368);(397,1225);(398,1144);(399,1170);(400,1088);(401,975);(402,916);(403,834);(404,790);(
        405,689);(406,632);(407,604);(408,592);(409,557);(410,507);(411,467);(412,367);(413,389);(414,309);(415,271);(416,236);(417,
        223);(418,218);(419,206);(420,164);(421,151);(422,127);(423,109);(424,99);(425,78);(426,71);(427,68);(428,57);(429,51);(430,
        43);(431,42);(432,35);(433,30);(434,19);(435,28);(436,16);(437,22);(438,11);(439,12);(440,10);(441,8);(442,8);(443,5);(444,1)
        ;(445,6);(446,5);(447,2);(448,2);(449,1);(450,2);(451,3);(452,2)]

        real	99m41.799s
        user	97m55.327s
        sys	0m31.425s
        
  * Enough already: Alice is over-cautious. Which is good: it proves that she can definitely choose enough qbits to run the protocol reliably.
  * That took an hour and 40 minutes. Enough already. I'm convinced.
  
## Alice, Bob and naive Eve

This is the intervention everybody knows about. The quantum and classical channels that are connected to Alice in fact go to [Eve](#whyEve). She has quantum and classical channels connected to Bob. So she can potentially intervene on either of them, or just pass on messages from one to the other.

Eve knows the protocol. Like Bob she doesn't need to know anything about *M* or *n*: she can read qbits until she sees Alice's first classical message. 

If she just passes on the qbits she sees without measuring them, and passes on classical messages likewise, she is undectable, like a network node. If she measures the qbits before sending them, she will be detected with a probability of 1-1/2<sup>b</sup> where *b* is the average number of checkbits. If she tries to send messages on the classical channel, guessing the hash keys, she will be detected with a probability of 1-1/2<sup>5*w*</sup>. Because, with long messages, *b* is probably >> 5*w*, most people have concluded that QKD's strength is in the quantum channel. Maybe not, as we shall see later.

Naive Eve does indeed measure and re-transmit the qbits she receives. She is, of course, always detected. In those circumstances Alice doesn't encrypt and send *M*, so even if Eve could do stuff with the classical channel it wouldn't matter. In my simulation she doesn't even try, simply passing on messages which are sent to her.

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp naiveEve.qtp LogEve.qtp SystemAEB.qtp)

Note that the simulation runs the exact same Alice, Bob and their loggers as the Eve-free simulation did. The SystemAEB file runs Alice, Bob and naive Eve in parallel with their three loggers.

        length of message? 100
        length of a hash key? 0
        number of sigmas? 10
        number of trials? 100

        961 qbits per trial
        all done: 0 Eve's; 100 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); average check bits (Alice/Eve) 120 minimum check bits (Alice/Eve) 97 average check bits (Eve/Bob) 120 minimum check bits (Eve/Bob) 97
        histogram of check-bit lengths (Alice/Eve)
        [(97,1);(100,1);(102,1);(106,1);(107,3);(108,3);(109,1);(110,2);(111,3);(112,4);(113,2);(114,3);(115,6);(116,2);(117,4);(118,4);(
        119,7);(120,5);(121,2);(122,7);(123,3);(124,4);(125,1);(126,3);(127,2);(128,2);(129,5);(130,3);(131,4);(134,2);(136,3);(137,2);(
        139,1);(144,1);(145,1);(148,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(97,1);(100,1);(102,1);(106,1);(107,3);(108,3);(109,1);(110,2);(111,3);(112,4);(113,2);(114,3);(115,6);(116,2);(117,4);(118,4);(
        119,7);(120,5);(121,2);(122,7);(123,3);(124,4);(125,1);(126,3);(127,2);(128,2);(129,5);(130,3);(131,4);(134,2);(136,3);(137,2);(
        139,1);(144,1);(145,1);(148,1)]

        real	0m21.518s
        user	0m2.955s
        sys	0m0.039s

  * Alice has gone for super-safety in the number of qbits she uses. Not much point because she detects interference _every_ time.
  
## Alice, Bob and quite clever Eve

It occurred to me that it would be possible for Eve to stand between Alice and Bob, playing Bob to Alice and Alice to Bob, _if_ she could write properly-tagged messages on the classical channel. That's a very big if: 1/2<sup>5*w*</sup> and all that. But suppose that she was listening on a parabolic microphone in the park in Zurich when Alice told Bob the passphrase and the number of bits per key, and suppose that she intervenes in every one of their exchanges from the very first. Then, of course, she won't be detected by any of the means discussed above: there won't be any interference on the quantum channels Alice->Eve and Eve->Bob (supposing no littler Eves in the way) and she can tag her pretend-Bob messages just as if she were Bob. Because there are, in effect, two QKD protocols running in parallel (one Alice<->Eve and the other Eve<->Bob) the two sides won't ever use the same codes nor the same hash keys after the first run. But that's no problem: it's easy to remember 10*w* hash-key bits.

My first attempt at a clever Eve wasn't quite successful, although in the simulation she is never detected, she always reads and decrypts Alice's message and she always recrypts it for Bob. I haven't yet, for full verisimilitude, simulated the Wegman-Carter hashing mechanism but that doesn't take away Eve's achievement because, when I do, I'll get the exact same results.

Like naive Eve she doesn't need information about *M* or *n*. But Eve isn't clever enough (or rather, her inventor wasn't clever enough). I thought at first that Alice would always use _all_ her code bits (less the ones she needs to keep for next time's hash keys) to encrypt the message she sends to Bob, and that Bob would expect a message that is as long as his code-bit sequence (take away the hash keys). So if Eve agrees more code bits with Bob than she does with Alice she is in trouble: Bob controls the number of code bits in QKD, and she can't get Alice to agree more code bits once they've exchanged bases. So in desperation she has to force Bob to restart the protocol. This is very unsatisfactory: as we saw above, it's easy for Alice to use so many qbits that retries are vanishingly unlikely. An  'Alice' who requests restarts ought perhaps to be suspected of being an Eve.

Because this Eve wants Alice->Eve to have the same number of code bits as Eve->Bob, the mask she fakes and sends to Alice selects sometimes many fewer, and sometimes many more, values than Bob would have askked for. So the histogram of check-bit-subsequence lengths doesn't look normal, and that's a dead giveaway.

        length of message? 1000
        length of a hash key? 0
        number of sigmas? 10
        number of trials? 1000

        4096 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); average check bits (Alice/Eve) 511 minimum check bits (Alice/Eve) 364 average check bits (Eve/Bob) 511 minimum check bits (Eve/Bob) 444
        histogram of check-bit lengths (Alice/Eve)
        [(364,1);(389,1);(394,1);(395,1);(399,1);(400,1);(403,1);(407,2);(413,2);(414,1);(416,1);(417,1);(418,1);(422,5);(423,4);(424
        ,2);(425,1);(426,1);(427,1);(428,2);(429,2);(430,1);(431,4);(432,2);(433,1);(434,3);(435,3);(436,3);(437,4);(438,3);(440,2);(
        441,3);(443,4);(444,3);(445,4);(446,6);(447,3);(448,3);(449,3);(450,2);(451,2);(452,4);(453,2);(454,3);(455,1);(456,5);(457,4
        );(458,5);(459,4);(461,2);(462,9);(463,3);(464,6);(465,6);(466,5);(467,4);(468,6);(469,7);(470,6);(471,7);(472,4);(473,3);(
        474,8);(475,6);(476,12);(477,6);(478,4);(479,6);(480,7);(481,5);(482,9);(483,9);(484,5);(485,6);(486,4);(487,13);(488,8);(489
        ,4);(490,11);(491,6);(492,8);(493,9);(494,12);(495,4);(496,10);(497,7);(498,6);(499,9);(500,10);(501,4);(502,10);(503,7);(504
        ,15);(505,8);(506,18);(507,7);(508,4);(509,9);(510,6);(511,8);(512,10);(513,10);(514,11);(515,12);(516,6);(517,15);(518,7);(
        519,9);(520,8);(521,11);(522,16);(523,9);(524,16);(525,5);(526,6);(527,13);(528,5);(529,6);(530,13);(531,9);(532,8);(533,13);
        (534,7);(535,8);(536,5);(537,5);(538,8);(539,6);(540,4);(541,10);(542,5);(543,6);(544,5);(545,9);(546,8);(547,7);(548,8);(549
        ,7);(550,10);(551,4);(552,5);(553,5);(554,6);(555,2);(556,5);(557,2);(558,3);(559,3);(560,5);(561,6);(562,7);(563,4);(564,1);
        (565,9);(566,3);(568,4);(569,2);(570,4);(571,3);(572,5);(573,2);(574,3);(575,5);(576,4);(578,4);(579,3);(580,5);(581,4);(583,
        4);(584,1);(585,3);(586,1);(587,5);(588,5);(589,2);(590,3);(593,1);(594,2);(595,1);(596,2);(597,1);(598,2);(600,3);(604,2);(
        607,2);(608,3);(609,1);(610,1);(611,1);(612,2);(613,1);(614,1);(615,2);(618,1);(621,1);(633,1);(634,1);(638,1);(658,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(444,1);(449,1);(453,1);(456,1);(459,1);(460,1);(461,2);(462,3);(464,2);(466,2);(467,1);(468,4);(469,1);(470,5);(471,4);(472
        ,1);(473,2);(474,4);(475,3);(476,12);(477,5);(478,6);(479,4);(480,9);(481,6);(482,8);(483,7);(484,11);(485,11);(486,8);(487,7
        );(488,6);(489,8);(490,9);(491,10);(492,12);(493,19);(494,15);(495,16);(496,16);(497,18);(498,13);(499,20);(500,20);(501,14);
        (502,15);(503,17);(504,21);(505,15);(506,23);(507,13);(508,22);(509,16);(510,20);(511,16);(512,18);(513,22);(514,21);(515,23)
        ;(516,13);(517,20);(518,18);(519,18);(520,18);(521,15);(522,15);(523,18);(524,12);(525,18);(526,15);(527,14);(528,16);(529,6)
        ;(530,9);(531,10);(532,12);(533,14);(534,15);(535,6);(536,6);(537,15);(538,14);(539,10);(540,8);(541,5);(542,5);(543,5);(544,
        3);(545,2);(546,5);(547,4);(548,4);(549,1);(550,6);(551,2);(552,2);(553,6);(554,3);(555,3);(556,1);(557,4);(558,2);(559,1);(
        560,1);(562,2);(563,2);(565,1);(573,2);(581,1)]

        real	2m53.837s
        user	2m33.970s
        sys	0m1.630s

  * with a nice long message and a safety-first Alice (10 &sigma;s) there are no retries. But 'clever' Eve's check-bit sequences are anomalous: much wider histogram, and not at all the same shape. If I were Alice I'd suspect an Eve.
  
        length of message? 100
        length of a hash key? 0
        number of sigmas? 0
        number of trials? 1000

        289 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 167 repetitions (Alice-Eve); 168 repetitions (Eve-Bob); average check bits (Alice/Eve) 34 minimum check bits (Alice/Eve) 2 average check bits (Eve/Bob) 35 minimum check bits (Eve/Bob) 19
        histogram of check-bit lengths (Alice/Eve)
        [(2,3);(6,3);(8,1);(9,2);(10,2);(11,9);(12,8);(13,7);(14,9);(15,6);(16,10);(17,12);(18,9);(19,10);(20,12);(21,30);(22,21);(23
        ,17);(24,20);(25,30);(26,22);(27,35);(28,28);(29,24);(30,27);(31,30);(32,42);(33,35);(34,47);(35,31);(36,43);(37,43);(38,32);
        (39,21);(40,43);(41,28);(42,20);(43,27);(44,21);(45,19);(46,21);(47,19);(48,20);(49,14);(50,17);(51,9);(52,18);(53,11);(54,10
        );(55,3);(56,3);(57,3);(58,3);(59,3);(60,1);(61,2);(63,2);(65,2)]
        histogram of check-bit lengths (Eve/Bob)
        [(19,1);(21,3);(22,1);(23,1);(24,6);(25,11);(26,18);(27,24);(28,39);(29,41);(30,36);(31,46);(32,46);(33,66);(34,67);(35,83);(
        36,68);(37,58);(38,76);(39,52);(40,45);(41,46);(42,39);(43,31);(44,21);(45,24);(46,15);(47,13);(48,5);(49,7);(50,4);(51,5);(
        54,1);(55,1)]

        real	0m35.300s
        user	0m12.470s
        sys	0m0.170s

  * With a shorter message and a careless Alice (0 &sigma;s) there are restarts, but no more from Eve than from Alice (Bob can't initiate them). So nothing to suspect here, were it not for the histogram. The shortest check-bit sequence that Bob generates is 19; Eve generates one of length 2, way, way outside the expected range. Bob goes up to 55, Eve to 65. Eve is bang to rights: Alice should nab her. 

        length of message? 3
        length of a hash key? 0
        number of sigmas? 0
        number of trials? 1000

        16 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 33 repetitions (Alice-Eve); 1143 repetitions (Eve-Bob); average check bits (Alice/Eve) 2 minimum check bits (Alice/Eve) 0 average check bits (Eve/Bob) 2 minimum check bits (Eve/Bob) 0
        histogram of check-bit lengths (Alice/Eve) [(0,183);(1,208);(2,168);(3,139);(4,127);(5,82);(6,51);(7,30);(8,9);(9,3)]
        histogram of check-bit lengths (Eve/Bob) [(0,106);(1,230);(2,277);(3,206);(4,130);(5,40);(6,5);(7,4);(8,2)]

        real	0m15.515s
        user	0m1.822s
        sys	0m0.043s
  
  * To give statistical variation full rein, I can use a ridiculously short message and 0 &sigma;s. Alice provokes 33 repetitions and Eve more repetitions than trials. Bob should spot her, though Alice probably wouldn't: her histogram is silly but then so is Bob's.

_Definitely_ no cigar.

## Alice, Bob and cleverer Eve

In the simulation I can make Alice careful or careless. In reality she is likely to be careful, and generate far more code bits than she strictly needs. If she is careless and generates too few, she'll have to restart. So Eve shouldn't worry: just let Alice control things. Play Bob to Alice and Alice to Bob, confident that in either direction there will be plenty of code bits to deal with the *M* that Alice has in mind, or if not, a restart won't be totally unexpected.

So cleverer Eve doesn't fake a mask when dealing with Alice: instead she does exactly what Bob would do, selecting check bits with probability 1/4. And when dealing with Bob she's just another Alice, agreeing a code as he directs. There is a possibility, if Alice is deliberately careless, that sometimes Alice could agree enough code bits with Eve to encrypt *M* when Eve and Bob did not. In that case Eve would have to ask Bob to restart. But also in that case Alice would be likely to provoke restarts of her own. It's not clear that Bob could spot Eve, though perhaps there might be a pre-agreed scenario where Alice and Bob agree to be risky between 9am and 9.30, and if Bob sees more restarts in that interval than he expects, Eve could be unveiled. 

        length of message? 1000
        length of a hash key? 0
        number of sigmas? 10
        number of trials? 1000

        4096 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); average check bits (Alice/Eve) 511 minimum check bits (Alice/Eve) 430 average check bits (Eve/Bob) 512 minimum check bits (Eve/Bob) 441
        histogram of check-bit lengths (Alice/Eve)
        [(430,1);(454,1);(455,1);(458,1);(459,1);(462,1);(464,2);(465,1);(466,1);(467,1);(468,1);(469,3);(470,3);(471,2);(472,3);(473
        ,1);(474,4);(475,6);(476,4);(478,9);(479,9);(480,5);(481,8);(482,12);(483,5);(484,12);(485,7);(486,11);(487,11);(488,12);(489
        ,9);(490,15);(491,10);(492,9);(493,13);(494,12);(495,11);(496,16);(497,14);(498,14);(499,23);(500,22);(501,19);(502,19);(503,
        13);(504,22);(505,11);(506,14);(507,23);(508,28);(509,14);(510,23);(511,17);(512,19);(513,18);(514,13);(515,12);(516,25);(517
        ,14);(518,14);(519,17);(520,16);(521,20);(522,9);(523,21);(524,20);(525,12);(526,11);(527,13);(528,18);(529,14);(530,14);(531
        ,7);(532,11);(533,8);(534,15);(535,8);(536,11);(537,11);(538,14);(539,6);(540,8);(541,7);(542,2);(543,4);(544,6);(545,7);(546
        ,5);(547,7);(548,7);(549,6);(550,3);(551,6);(552,5);(553,4);(554,3);(555,3);(556,3);(557,2);(558,2);(559,1);(560,2);(561,1);(
        562,2);(566,1);(571,1);(589,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(441,1);(445,1);(449,1);(452,1);(454,1);(455,1);(456,1);(457,1);(458,1);(463,1);(464,1);(465,2);(466,1);(467,1);(468,3);(469
        ,4);(470,1);(471,3);(472,1);(473,3);(475,1);(476,3);(477,4);(478,5);(479,10);(480,9);(481,8);(482,8);(483,6);(484,8);(485,7);
        (486,11);(487,12);(488,5);(489,5);(490,6);(491,13);(492,12);(493,14);(494,12);(495,15);(496,18);(497,13);(498,25);(499,18);(
        500,16);(501,17);(502,16);(503,11);(504,18);(505,23);(506,22);(507,15);(508,16);(509,23);(510,14);(511,18);(512,10);(513,22);
        (514,18);(515,17);(516,13);(517,17);(518,22);(519,20);(520,25);(521,18);(522,16);(523,13);(524,17);(525,16);(526,15);(527,21)
        ;(528,13);(529,12);(530,12);(531,14);(532,16);(533,16);(534,14);(535,8);(536,7);(537,6);(538,7);(539,7);(540,8);(541,7);(542,
        7);(543,5);(544,7);(545,3);(546,8);(547,2);(548,6);(549,5);(550,8);(551,1);(552,2);(553,2);(554,3);(556,6);(557,5);(559,3);(
        561,3);(562,2);(563,2);(564,1);(568,1);(569,2);(572,1);(574,1)]

        real	3m13.109s
        user	2m43.113s
        sys	0m1.806s

  * With cautious Alice and a long message Eve can hide perfectly. Her histogram looks a bit wide, but it must be within normal limits because she is exactly playing Bob.
  
        length of message? 100
        length of a hash key? 0
        number of sigmas? 0
        number of trials? 1000

        289 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 165 repetitions (Alice-Eve); 320 repetitions (Eve-Bob); average check bits (Alice/Eve) 35 minimum check bits (Alice/Eve) 19 average check bits (Eve/Bob) 35 minimum check bits (Eve/Bob) 20
        histogram of check-bit lengths (Alice/Eve)
        [(19,1);(22,4);(23,3);(24,6);(25,8);(26,18);(27,22);(28,28);(29,33);(30,45);(31,55);(32,59);(33,56);(34,72);(35,79);(36,83);(
        37,59);(38,70);(39,53);(40,55);(41,49);(42,36);(43,29);(44,28);(45,14);(46,6);(47,11);(48,6);(50,7);(51,1);(52,2);(54,2)]
        histogram of check-bit lengths (Eve/Bob)
        [(20,1);(21,1);(22,1);(23,4);(24,3);(25,11);(26,30);(27,23);(28,23);(29,42);(30,35);(31,69);(32,55);(33,73);(34,73);(35,53);(
        36,70);(37,63);(38,76);(39,66);(40,57);(41,45);(42,37);(43,23);(44,19);(45,17);(46,11);(47,6);(48,6);(49,1);(50,3);(51,1);(53
        ,1);(54,1)]

        real	1m3.412s
        user	0m13.962s
        sys	0m0.179s
        
  * With mad Alice and a shorter message and she can be spotted. Bob should know that with 289 qbits he's in a 0-%sigma; game and can expect about 150 restarts. But he's seeing 320: all Alice's and about the same number from Eve. She can be spotted.

        length of message? 3
        length of a hash key? 0
        number of sigmas? 0
        number of trials? 1000

        16 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 37 repetitions (Alice-Eve); 70 repetitions (Eve-Bob); average check bits (Alice/Eve) 2 minimum check bits (Alice/Eve) 0 average check bits (Eve/Bob) 1 minimum check bits (Eve/Bob) 0
        histogram of check-bit lengths (Alice/Eve) [(0,98);(1,258);(2,322);(3,196);(4,84);(5,33);(6,8);(7,1)]
        histogram of check-bit lengths (Eve/Bob) [(0,140);(1,240);(2,308);(3,194);(4,85);(5,26);(6,7)]

        real	0m49.318s
        user	0m1.208s
        sys	0m0.029s
        
  * With a ridiculously short message the same pattern: twice as many restarts for Bob as he might expect.
  
So cleverer Eve is not yet clever enough. But there may yet be a counter-counter-measure that Eve can try. I haven't got one yet. If Eve stops playing for a while as soon as she sees an Alice-provoked restart then she will avoid detection but she will also lose her place in the hash-key generation sequence, and she won't get back in. In the spying world that might be enough: burn the code books and run. At least she will have seen all the messages up to then.

<a name="whyEve"></a>
## Why "Eve"?

"Eve" from "eavesdropper"? I do hope so. Not, I hope, from any notion of females as deceptive.
