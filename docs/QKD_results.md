(I've deleted the html version of this file because git's rendering of this file is superior to an html browser's. So it's available at  

    github.com/mdxtoc/qtpi/blob/master/docs/QKD_results.md  
    
But if you are reading this then you already know that ...)

# Experiments with QKD

I've encoded QKD in qtpi, and played around with it. The simulation has taught me a lot. I thought for a while that [I had found a (tiny) security hole](#cleverEve), and then that [I had made it a little bigger](#superEve), then I thought that [I probably hadn't](#notreally), and then that I should [try it out](#whataboutit).

But actually [it's codswallop](#codswallop). My 'security hole' is the way the protocol is supposed to work, daisy-chaining A&harr;B, B&harr;C, ... Y&harr;Z. Obviously each of those components has to be trusted; obviously if any is dishonest the whole chain is compromised. The research community is well aware of the problem, and well on top of it. So egg on my face. But I enjoyed my experiments, and I enjoyed building a tool which could carry them out.

## The scenario

Alice has a message *M* which she wants to send to Bob. She has a quantum channel to him, and a [Wegman-Carter hash-tagged](#wegmancarter) two-way classical channel to him. She [calculates the number of qbits she will need](#enoughqbits), and sends them, one at a time and picking measurement basis and value for each at random, to Bob. Bob separately picks a random basis for each qbit, measures it in that basis, and records the results.

Then they do the QKD protocol dance: Alice sends the bases she chose to Bob through the classical channel and Bob sends the bases he chose back to Alice. They each select the subsequence of values for which they used the same basis, which will be about half of them, and throw the rest away. Now, supposing no interference with the qbits in transit, and no interference with the classical messages, they share the same sequence of code bits. Bob picks a subsequence of his code bits, sends a bit-mask to Alice to characterise it, and the subsequence itself. Alice looks at the corresponding subsequence of her own code bits: if they have the same code bits then the two subsequences should be identical, with probability 1-1/2<sup>*c*</sup>, where *c* is the number of bits Bob picks. If the subsequences differ, and nothing is wrong with the classical communication, then something has interfered with Alice's quantum transmissions.

If all seems ok Alice deletes Bob's checkbits from her code bits, takes a prefix of what's left to exclusive-or mask the message *M*, and sends it down the classical channel to Bob. Bob, having deleted his checkbits from his own code bits, takes a prefix of the same length as Alice's communication, exclusive-or's the two, and he can see *M*. 

<a name="hashsecret"></a>
Before the protocol started Alice and Bob shared a secret: five 'short' one-time hash keys, one for each of the five classical messages they exchange (bases A&rarr;B, bases B&rarr;A, bit-mask B&rarr;A, subsequence B&rarr;A, encrypted message A&rarr;B). Each classical message is tagged by a hash of the message controlled by the corresponding hash key, and each tag is checked by the recipient, who uses the same hash function and knows the same hash key. If the tags aren't as expected then something is spoofing messages on the classical channel. If all is ok when the protocol is over, Alice and Bob each take five new hash keys from the unused suffix of their code bits, and they are ready to run the protocol again. Crucially, the classical messages are sent in the clear, but the secret code bits are never disclosed, apart from the checkbit sequence sent by Bob.

If there is an eavesdropper Eve, then the quantum and classical channels lead through her. She must do her best to read the quantum traffic between Alice and Bob, and to intercept and alter classical messages, and do it all without being noticed.

In the simulation we log the steps of the protocol, so our Alice, Bob and Eve each have a classical bit-list channel back to a logging process. In reality Alice and/or Bob would fall silent if they detected interference, but in the simulation we complete each trial even if something seems to be wrong. So Alice sends a blank (zero-length) message instead of an encrypted *M* if she detects quantum-channel interference, and each of them keeps going even if they detect classical-channel interference. 

In the real world Alice would be sure to pick enough qbits to ensure near certainty that Bob can select enough check bits to reliably detect interference, and to give her enough code bits to encrypt *M* and refresh the bit sequences. In the simulation she may be directed to pick too few, and she and Bob share a signalling channel (which also goes through Eve, if she's present) so that they can restart the experiment if Alice doesn't have enough code bits. 

Restarting is not part of the QKD protocol. It would be a security risk, because Alice and Bob would have to re-use what should be one-time hash keys, and multiple re-use might give an eagle-eyed interceptor enough information to hack the classical channel. It's in the simulation just to allow experiment with calculating qbit numbers: see the [description of Alice's calculation](#enoughqbits) for an analysis of repetition frequency and see the [no Eve trials](#noEve) for some experimental results.

<a name="enoughqbits"></a>
## Picking enough qbits

Suppose Alice's message *M* is *m* bits long, and that the Wegman-Carter one-time hash keys are each *w* bits long, so she needs at least

&emsp;&emsp;*k* = *m*+5*w*

secret code bits: *m* to encrypt *M* and send it to Bob, 5*w* to use for new hash keys. if *n* is the number of qbits she sends, then she can expect that about *n*/2 code bits will be agreed with Bob, who will then take a proportion of those -- in our simulation a quarter or *n*/8 -- for check bits. So *n*/2 - *n*/8 = 3*n*/8 has to be at least *k*. (Actually she would probably have a minimum number *c* of checkbits in mind, to ensure that the quantum-interference check is reliable, so that puts a lower bound on *n*/8, but we can deal with that by putting a lower bound on *n* after we've calculated it.)

She must also allow for statistical variation: sometimes she and Bob will agree less, sometimes more, code bits. She knows that the standard deviation &sigma; of the number of successes when choosing with probability *p* from a sequence length *n* is &radic;<span style="text-decoration:overline;">&nbsp;*np*(1-*p*)&nbsp;</span>. She wants the probability of choosing too few bits to be very small, so she must over-estimate. If she wants to be *s* &sigma;s away from trouble, well into the tail of the normal distribution, she can write some equations. 

First, Bob may choose more than *n*/8 bits: he chooses a bit with probability 1/4 from a sequence length *n*/2, so the worst-case pick that she has to allow for is

&emsp;&emsp;*b* = *n*/8 + *s*&radic;<span style="text-decoration:overline;">&nbsp;*n*/2(1/4)(3/4)&nbsp;</span>   

&emsp;&emsp;&emsp;&ensp;= *n*/8 + *s*&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>

If *s* is large enough Bob won't pick more than that many bits very often: [famously](https://en.wikipedia.org/wiki/68–95–99.7_rule) for *s*=5 the chances are 0.00003%, and they go down about three orders of magnitude for every increase in *s* after that. So Alice can give herself a comfortable allowance by choosing *s*=8 or *s*=10, or whatever she likes.

Alice and Bob will agree on the measurement basis for a qbit with probability 1/2. There will be statistical variation in the number of bits they agree on, and she must make sure that the number she needs is in the tail of the normal distribution, *s* &sigma;s away from the mean. So she can calculate 

&emsp;&emsp;*n*/2 &ge; *k* + *b* + *s*&radic;<span style="text-decoration:overline;">&nbsp;*n*(1/2)(1/2)&nbsp;</span>

&emsp;&emsp;&emsp;&ensp;= *k* + *b* + *s*/2&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>

&emsp;&emsp;&emsp;&ensp;= *k* + *n*/8 + *s*(&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>+1/2)&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span> 

Taking the inequality as an equality, this is a quadratic in &radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>:

&emsp;&emsp;3/8*n* - *s*(&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>+1/2)&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span> - *k* = 0

One of the solutions of this equation is negative, so we ignore it and take the positive solution: now that qtpi's *num* type includes both integers and unbounded-precision rationals, she can calculate the root directly. (Of course we still use an approximation for *sqrt*.) 

At this point Alice has to decide if she will get enough check-bits from Bob. She can be sure of

&emsp;&emsp;*c* = *n*/8 - *s*&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>

So, given a pre-arranged lower bound *cmin*, she can calculate a lower bound *nmin* from a quadratic in &radic;<span style="text-decoration:overline;">&nbsp;*nmin*&nbsp;</span>

&emsp;&emsp;*nmin*/8 - *s*&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>&radic;<span style="text-decoration:overline;">&nbsp;*nmin*&nbsp;</span> - *cmin* = 0

This gives quite a large lower bound: e.g. with *cmin*=20, *s*=10, we have *nmin*=891. 

The [no Eve trials](#noEve) show how many bits she uses for various values of *k*, *s* and *cmin*, and how it affects the repetition rate.

<a name="wegmancarter"></a>
## Wegman-Carter hash-tagging

For verisimilitude I implement hash tagging. But it doesn't make a difference: in the simulation Eve can either hack it perfectly ([clever Eve](#cleverEve) and [cleverer Eve](#superEve)) or she doesn't even try ([naive Eve](#naiveEve)).

Wegman-Carter tagging seems too computationally expensive whilst qtpi is a naively interpreted language (but watch this space now that qtpi can compute with rationals ...). So I do something simpler, because I'm not simulating security against code-crackers. It's still a hash, and experiment shows that if Eve accidentally gets her keys muddled up, Alice and Bob notice.

For a hash-key size *w* choose packet size *p* = *w*/3\*4+1. Divide the bit sequence to be hashed into packets size 2*p*; convert each packet to an integer; multiply by the hash key; mask with 2<sup>*p*</sup>-1 to reduce the size of the result; convert back to bit strings and concatenate. That will have reduced the size of the bit-string by half. Repeat until you have no more than *p* bits, and that's the tag. 

<a name="noEve"></a>
## No Eve: just Alice and Bob

Trials to see if Alice picks enough qbits. Interference never detected because Eve isn't there: command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                    SystemAB.qtp)

Note that in this simulation Bob doesn't know the length of *M*, still less the number of qbits Alice is going to send him. He reads qbits until he sees Alice's first message on the classical channel. Oh, the power of guarded sums!

### With hash tags

  * With hash tagging, the hash calculations are implemented in the qtpi functional language and therefore slowly interpreted.
  But it works: Bob and Alice each agree that the other isn't spoofing classical messages.
  
        length of message? 4000
        length of a hash key? 12
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        13306 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 0 repetition(s); average check bits 1665.39 minimum check bits 1561
        histogram of check-bit lengths
        [(1561,1);(1577,1);(1580,1);(1587,1);(1589,1);(1591,1);(1598,1);(1600,1);(1606,1);(1609,1);(1612,1);(1615,1);(1617,1);(1619,2
        );(1620,1);(1624,1);(1625,1);(1626,2);(1628,2);(1632,2);(1633,1);(1637,1);(1639,1);(1641,2);(1644,2);(1646,1);(1648,2);(1649,
        2);(1650,1);(1653,2);(1654,1);(1655,1);(1657,3);(1659,1);(1660,2);(1663,2);(1664,2);(1665,1);(1666,1);(1668,1);(1670,1);(1672
        ,2);(1673,2);(1674,2);(1675,2);(1676,1);(1679,1);(1680,1);(1681,1);(1682,1);(1683,1);(1684,1);(1685,1);(1686,1);(1688,1);(
        1689,1);(1690,2);(1691,1);(1694,1);(1696,1);(1697,2);(1703,1);(1706,1);(1707,1);(1708,1);(1709,1);(1712,1);(1715,1);(1717,1);
        (1719,1);(1721,1);(1727,1);(1733,1);(1734,1);(1745,1);(1754,2);(1762,1);(1789,1);(1790,1)]

        real	1m6.485s
        user	0m42.363s
        sys	0m0.503s
  
  * That's about 4 seconds for each trial, but it is 1.3M qbits in 45 seconds. It is a quarter faster without hash tagging (zero-length keys turn it off) or, if you like, a third slower with hash tagging.

        length of message? 4000
        length of a hash key? 0
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        13130 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 0 repetition(s); average check bits 1639.60 minimum check bits 1531
        histogram of check-bit lengths
        [(1531,1);(1554,1);(1569,1);(1570,1);(1585,1);(1588,1);(1591,1);(1592,1);(1594,2);(1595,2);(1596,1);(1597,1);(1604,1);(1605,1
        );(1606,1);(1607,2);(1609,1);(1611,1);(1613,1);(1614,1);(1617,3);(1618,1);(1619,1);(1620,1);(1621,2);(1622,1);(1624,1);(1626,
        1);(1627,1);(1629,1);(1630,2);(1631,3);(1633,1);(1634,2);(1635,3);(1637,1);(1639,2);(1640,1);(1641,2);(1644,1);(1646,3);(1647
        ,1);(1648,2);(1651,1);(1652,3);(1653,2);(1654,1);(1657,1);(1659,3);(1660,1);(1661,1);(1662,1);(1663,1);(1664,1);(1665,1);(
        1666,2);(1667,1);(1668,2);(1670,1);(1671,1);(1672,1);(1673,1);(1676,2);(1679,1);(1681,1);(1682,2);(1689,1);(1694,1);(1698,1);
        (1699,1);(1707,1);(1721,1);(1723,1);(1730,1)]

        real	1m1.062s
        user	0m33.069s
        sys	0m0.434s

  * Even though the hash tagging mechanism is affordable it's turned off in many of the experiments below.
  
### 0 Sigma  
* Checking the *cmin* &rarr; *nmin* calculation, and the lower-bounding. It works.

        length of message? 1
        length of a hash key? 0
        minimum number of checkbits? 20
        number of sigmas? 10
        number of trials? 1
        with commentary (y/n)? n

        891 qbits
        all done: 0 interfered with; 1 exchanges succeeded; 0 failed; 0 repetition(s); average check bits 106.00 minimum check bits 106
        histogram of check-bit lengths [(106,1)]

        real	0m28.372s
        user	0m0.047s
        sys	0m0.009s

* With a medium-length message we get an immense repetition rate. 

        length of message? 100
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 100

        266 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 126 repetition(s); average check bits 32.45 minimum check bits 19
        histogram of check-bit lengths
        [(19,1);(23,4);(24,1);(26,4);(27,4);(28,6);(29,7);(30,5);(31,11);(32,9);(33,10);(34,5);(35,8);(36,5);(37,5);(38,6);(39,3);(40
        ,1);(42,1);(43,2);(44,1);(46,1)]

        real	0m16.915s
        user	0m1.382s
        sys	0m0.023s

 * With a very short message we get slightly fewer repetitions.

        length of message? 3
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 100
  
        7 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 75 repetition(s); average check bits 0.74 minimum check bits 0
        histogram of check-bit lengths [(0,51);(1,29);(2,15);(3,5)]

        real	0m16.233s
        user	0m0.156s
        sys	0m0.008s
 
  * With a longer message, and therefore many more qbits, it's possible to see that the calculation of qbits is working accurately. The repetition rate is ridiculous, but that's a consequence of using 0 sigmas. 
   
        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        2666 qbits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 998 repetition(s); average check bits 329.55 minimum check bits 277
        histogram of check-bit lengths
        [(277,1);(279,1);(283,2);(284,1);(285,1);(287,1);(288,2);(289,2);(290,1);(291,2);(293,2);(294,1);(295,1);(296,3);(297,4);(298
        ,5);(299,4);(300,6);(301,1);(302,7);(303,5);(304,4);(305,12);(306,10);(307,19);(308,10);(309,10);(310,12);(311,15);(312,21);(
        313,22);(314,15);(315,15);(316,19);(317,20);(318,15);(319,18);(320,16);(321,16);(322,18);(323,21);(324,27);(325,27);(326,18);
        (327,22);(328,16);(329,20);(330,18);(331,29);(332,25);(333,20);(334,29);(335,20);(336,16);(337,22);(338,28);(339,22);(340,19)
        ;(341,17);(342,21);(343,19);(344,14);(345,23);(346,17);(347,12);(348,12);(349,10);(350,9);(351,14);(352,14);(353,8);(354,8);(
        355,5);(356,9);(357,1);(358,5);(359,3);(360,2);(361,8);(362,3);(363,1);(364,3);(365,3);(366,1);(367,4);(368,1);(369,3);(373,1
        );(374,2);(375,4);(378,1);(380,1);(382,1);(393,1)]

        real	2m40.891s
        user	2m8.381s
        sys	0m1.403s
        
### 1 Sigma

  * Attempting to swamp the rounding errors by choosing a longer message but 1 &sigma;. The repetition rate about 0.4%, which seems rather low. 
  
        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 1
        number of trials? 1000

        2780 qbits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 43 repetition(s); average check bits 347.95 minimum check bits 279
        histogram of check-bit lengths
        [(279,1);(297,1);(301,1);(304,2);(305,3);(306,1);(307,2);(309,5);(310,4);(311,2);(312,2);(313,2);(314,3);(315,3);(316,4);(317
        ,6);(318,4);(319,3);(320,5);(321,4);(322,9);(323,9);(324,14);(325,8);(326,12);(327,10);(328,12);(329,11);(330,9);(331,16);(
        332,13);(333,15);(334,21);(335,24);(336,20);(337,13);(338,27);(339,20);(340,9);(341,22);(342,17);(343,25);(344,36);(345,23);(
        346,24);(347,16);(348,16);(349,21);(350,27);(351,21);(352,31);(353,18);(354,27);(355,29);(356,17);(357,21);(358,18);(359,16);
        (360,15);(361,23);(362,10);(363,20);(364,12);(365,16);(366,13);(367,12);(368,5);(369,8);(370,7);(371,8);(372,6);(373,8);(374,
        12);(375,8);(376,8);(377,3);(378,7);(379,2);(380,8);(381,3);(382,5);(383,3);(384,1);(385,4);(386,2);(387,1);(388,1);(389,2);(
        390,1);(391,1);(392,3);(394,1);(395,1);(396,1);(398,1);(400,2);(415,1)]

        real	1m44.553s
        user	1m18.910s
        sys	0m0.783s
  
### 3 Sigma

* With a reasonably long message and small oodles of trials and only 3 &sigma; we see no repetitions. Enough already: Alice is over-cautious. Which is good: it proves that she can definitely choose enough qbits to run the protocol reliably.
* This test took over 12 minutes. That's enough. I'm convinced.

        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 3
        number of trials? 10000

        3022 qbits per trial
        all done: 0 interfered with; 10000 exchanges succeeded; 0 failed; 0 repetition(s); average check bits 377.47 minimum check
        bits 306
        histogram of check-bit lengths
        [(306,1);(314,1);(316,1);(317,1);(318,1);(319,2);(320,3);(321,3);(322,1);(323,4);(324,3);(325,1);(326,6);(327,8);(328,7);(329
        ,6);(330,1);(331,8);(332,9);(333,12);(334,16);(335,20);(336,20);(337,18);(338,24);(339,18);(340,25);(341,36);(342,39);(343,31
        );(344,35);(345,39);(346,47);(347,48);(348,73);(349,76);(350,74);(351,71);(352,68);(353,101);(354,79);(355,89);(356,114);(357
        ,124);(358,106);(359,134);(360,137);(361,168);(362,147);(363,168);(364,163);(365,190);(366,180);(367,160);(368,206);(369,177)
        ;(370,188);(371,190);(372,218);(373,226);(374,222);(375,197);(376,222);(377,277);(378,234);(379,205);(380,218);(381,219);(382
        ,203);(383,205);(384,195);(385,195);(386,206);(387,168);(388,187);(389,187);(390,168);(391,166);(392,178);(393,120);(394,134)
        ;(395,136);(396,124);(397,116);(398,97);(399,114);(400,104);(401,97);(402,100);(403,106);(404,80);(405,78);(406,76);(407,55);
        (408,47);(409,59);(410,44);(411,40);(412,39);(413,28);(414,25);(415,22);(416,30);(417,21);(418,22);(419,18);(420,10);(421,11)
        ;(422,9);(423,8);(424,9);(425,4);(426,4);(427,7);(428,6);(429,4);(430,5);(431,2);(432,2);(433,2);(434,2);(435,1);(436,1);(438
        ,2);(439,2);(448,1);(451,1);(474,1)]

        real	13m42.688s
        user	12m34.737s
        sys	0m8.639s
            
<a name="naiveEve"></a>
## Alice, Bob and naive Eve

This is the intervention everybody knows about. The quantum and classical channels that are connected to Alice in fact go to [Eve](#whyEve). She has quantum and classical channels connected to Bob. So she can potentially intervene on either of them, or just pass on messages from one to the other.

Eve knows the protocol, and she knows Alice's and Bob's implementation (but they don't know hers). Like Bob she doesn't need to know anything about *M* or *n*: she can read qbits until she sees Alice's first classical message. 

If she passes on the qbits she sees without measuring them, and passes on classical messages likewise, she is undectable, like a network node. If she measures the qbits before sending them, she will be detected with a probability of 1-1/2<sup>c</sup> where *c* is the number of checkbits Bob generates. If she tries to send messages on the classical channel, guessing the hash keys, she will be detected with a probability of 1-1/2<sup>5*w*</sup>. Because, with long messages and a suitably cautious Alice, *c* is probably >> 5*w*, most people have concluded that QKD's strength is in the quantum channel. Maybe not, as we shall see below.

Naive Eve does indeed measure and re-transmit the qbits she receives. She is, of course, pretty much always detected. Once she's spotted, Alice doesn't encrypt and send *M*, so even if Eve could hack the classical channel it wouldn't do her much good. In my simulation she simply re-transmits classical messages.

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                    naiveEve.qtp LogEve.qtp SystemAEB.qtp)

Note that the simulation runs the exact same Alice, Bob and their loggers as the Eve-free simulation did. The SystemAEB file runs Alice, Bob and naive Eve in parallel with their three loggers (though it's set up to deal with [cleverer Eve](#superEve), so naive Eve has to use two logging channels when she only really needs one).

  * Alice goes for super-safety in the number of qbits she uses. And then, of course, she detects interference _every_ time.
  
        length of message? 100
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        trial number 1 quantum interference detected -- 147 check bits
        trial number 2 quantum interference detected -- 187 check bits
            .....
        trial number 100 quantum interference detected -- 139 check bits
        
        1312 qbits per trial
        all done: 0 Eve's; 100 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); average check bits (Alice/Eve) 163.46; minimum check bits (Alice/Eve) 130; average check bits (Eve/Bob) 163.46; minimum check bits (Eve/Bob) 130
        histogram of check-bit lengths (Alice/Eve)
        [(130,1);(135,1);(137,1);(139,1);(144,4);(145,4);(146,1);(147,3);(148,1);(149,1);(150,2);(151,2);(152,2);(153,1);(154,1);(155
        ,1);(156,3);(157,3);(158,1);(159,3);(160,4);(161,2);(162,3);(163,3);(164,3);(165,2);(167,4);(168,4);(169,1);(170,2);(171,4);(
        172,4);(173,3);(174,1);(175,1);(176,1);(177,6);(178,3);(179,4);(180,1);(181,1);(182,1);(183,1);(186,1);(187,1);(194,2)]
        histogram of check-bit lengths (Eve/Bob)
        [(130,1);(135,1);(137,1);(139,1);(144,4);(145,4);(146,1);(147,3);(148,1);(149,1);(150,2);(151,2);(152,2);(153,1);(154,1);(155
        ,1);(156,3);(157,3);(158,1);(159,3);(160,4);(161,2);(162,3);(163,3);(164,3);(165,2);(167,4);(168,4);(169,1);(170,2);(171,4);(
        172,4);(173,3);(174,1);(175,1);(176,1);(177,6);(178,3);(179,4);(180,1);(181,1);(182,1);(183,1);(186,1);(187,1);(194,2)]

        real	0m49.414s
        user	0m5.100s
        sys	0m0.066s

<a name="cleverEve"></a>
## Alice, Bob and clever Eve

It occurred to me that it would be possible for Eve to stand between Alice and Bob, playing Bob to Alice and Alice to Bob, _if_ she could write properly-tagged messages on the classical channel. That's a very big if: 1/2<sup>5*w*</sup> and all that. But suppose that she was listening on a parabolic microphone in the park in Zurich when Alice told Bob the passphrase and the number of bits per key, and suppose that she intervenes in every one of their exchanges from the very first. Then, of course, she won't be detected by any of the means discussed above: there won't be any interference on the quantum channels Alice&rarr;Eve and Eve&rarr;Bob (supposing no littler Eves in the way) and she can tag her pretend-Alice and pretend-Bob messages just as if she were Alice or Bob. Because there are, in effect, two QKD protocols running in parallel (one Alice&harr;Eve and the other Eve&harr;Bob) the two sides won't use the same codes nor the same hash keys after the first run. But that's no problem: it's easy for Eve to remember 10*w* hash-key bits.

My first attempt at a clever Eve is never detected, always reads and decrypts Alice's message and almost always recrypts it for Bob.

Like naive Eve she doesn't need information about *M* or *n*. But Eve isn't clever enough (or rather, I wasn't clever enough). I thought that Alice would always use _all_ her code bits (less the ones she needs to keep for next time's hash keys) to encrypt the message she sends to Bob, so that Bob would expect a message that is as long as his code-bit sequence (take away the hash keys). If Eve agrees more code bits with Bob than she does with Alice then she is in trouble: Bob controls the number of code bits in QKD, and she can't get Alice to agree more code bits once they've exchanged bases. So in desperation she has to force Bob to restart the protocol. This is very unsatisfactory: as we saw above, it's easy for Alice to use so many qbits that retries are vanishingly unlikely. Bob should realise that a partner who requests restarts ought  to be suspected of being an Eve.

There is more. Because this Eve wants Alice&rarr;Eve to have the same number of code bits as Eve&rarr;Bob, the mask she fakes and sends to Alice selects sometimes many fewer, and sometimes many more, values than Bob would have asked for. So the histogram of check-bit-subsequence lengths doesn't look normal, and that's a dead giveaway.

The command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                cleverEve.qtp LogEve.qtp SystemAEB.qtp)

  * With a long message and a safety-first Alice (20-bit hash keys; 10 &sigma;s) there are no retries. But Eve's check-bit sequences are anomalous: she generates a checkbit histogram more than twice as wide as Bob's. If I were Alice I'd suspect an Eve.
  
        length of message? 1000
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 1000

        4351 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); average check bits (Alice/Eve) 543.17; minimum check bits (Alice/Eve) 411; average check bits (Eve/Bob) 544.43; minimum check bits (Eve/Bob) 482
        histogram of check-bit lengths (Alice/Eve)
        [(411,1);(418,1);(420,1);(424,1);(426,1);(432,1);(434,1);(439,1);(440,1);(443,1);(444,5);(445,1);(446,3);(448,2);(449,1);(450
        ,1);(451,1);(452,2);(453,2);(454,1);(455,3);(456,1);(457,1);(458,2);(460,1);(461,1);(462,3);(464,1);(465,2);(466,1);(467,2);(
        469,2);(470,2);(471,1);(472,1);(473,2);(474,7);(475,6);(476,5);(477,1);(478,1);(479,3);(480,5);(481,4);(482,3);(483,3);(484,3
        );(485,7);(487,7);(488,6);(489,7);(490,3);(491,7);(492,4);(493,7);(494,2);(495,7);(496,5);(497,6);(498,3);(499,4);(500,14);(
        501,6);(502,6);(504,10);(505,5);(506,5);(507,8);(508,8);(509,6);(510,9);(511,7);(512,3);(513,7);(514,8);(515,6);(516,7);(517,
        11);(518,5);(519,6);(520,8);(521,10);(522,5);(523,12);(524,7);(525,3);(526,5);(527,6);(528,9);(529,2);(530,9);(531,9);(532,6)
        ;(533,2);(534,7);(535,6);(536,9);(537,12);(538,15);(539,6);(540,7);(541,7);(542,5);(543,11);(544,8);(545,13);(546,13);(547,6)
        ;(548,10);(549,16);(550,4);(551,10);(552,9);(553,7);(554,14);(555,8);(556,10);(557,6);(558,9);(559,5);(560,5);(561,10);(562,7
        );(563,11);(564,10);(565,4);(566,9);(567,13);(568,11);(569,7);(570,9);(571,10);(572,8);(573,5);(574,8);(575,6);(576,8);(577,7
        );(578,3);(579,5);(580,8);(581,8);(582,11);(583,4);(584,9);(585,4);(586,7);(587,8);(588,6);(589,5);(590,5);(591,7);(592,5);(
        593,2);(594,3);(595,3);(596,3);(597,1);(598,3);(599,6);(600,6);(601,2);(602,2);(603,2);(604,4);(605,6);(606,1);(607,3);(608,4
        );(609,1);(611,3);(612,4);(613,4);(614,2);(615,1);(616,2);(617,3);(618,2);(620,4);(621,2);(622,3);(623,1);(624,1);(625,2);(
        626,3);(627,2);(629,1);(630,2);(631,1);(632,1);(633,2);(634,1);(635,1);(638,2);(639,1);(640,1);(641,2);(642,2);(643,1);(644,1
        );(647,2);(648,1);(653,1);(654,1);(656,1);(665,1);(671,1);(675,1);(678,1);(680,1);(698,1);(701,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(482,1);(483,1);(485,1);(486,2);(490,1);(491,1);(492,1);(493,2);(496,1);(497,2);(498,2);(500,3);(501,3);(502,2);(503,3);(504
        ,5);(505,3);(507,6);(508,3);(509,6);(510,3);(511,8);(512,3);(513,10);(514,12);(515,11);(516,10);(517,6);(518,7);(519,16);(520
        ,18);(521,11);(522,14);(523,6);(524,13);(525,7);(526,13);(527,16);(528,15);(529,13);(530,9);(531,20);(532,19);(533,9);(534,16
        );(535,11);(536,16);(537,21);(538,16);(539,19);(540,16);(541,14);(542,15);(543,22);(544,18);(545,17);(546,20);(547,19);(548,
        21);(549,11);(550,17);(551,17);(552,16);(553,18);(554,15);(555,21);(556,16);(557,10);(558,10);(559,17);(560,11);(561,20);(562
        ,15);(563,11);(564,11);(565,9);(566,10);(567,8);(568,13);(569,14);(570,11);(571,6);(572,8);(573,11);(574,9);(575,9);(576,8);(
        577,5);(578,6);(579,7);(580,4);(581,4);(582,1);(583,5);(584,2);(585,2);(586,1);(587,1);(588,7);(590,5);(591,1);(592,1);(593,3
        );(594,1);(595,3);(596,1);(597,1);(598,2);(600,2);(603,1);(604,1);(606,1);(614,1)]

        real	4m15.174s
        user	3m43.412s
        sys	0m2.395s

  * With a shorter message and a careless Alice (0 &sigma;s; no hashing; no checkbit minimum) there are restarts, but hardly any more from Eve than from Alice. So nothing to suspect here, were it not for the histogram. The shortest check-bit sequence that Bob generates is 19; Eve generates one of length 2, way, way outside the expected range. Bob goes up to 58, Eve to 67. Eve is bang to rights: Alice should nab her.
  
        length of message? 100
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        266 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 993 repetitions (Alice-Eve); 995 repetitions (Eve-Bob); average check bits (Alice/Eve) 27.43; minimum check bits (Alice/Eve) 2; average check bits (Eve/Bob) 32.10; minimum check bits (Eve/Bob) 18
        histogram of check-bit lengths (Alice/Eve)
        [(2,3);(3,3);(4,3);(6,4);(7,9);(8,6);(9,6);(10,9);(11,10);(12,14);(13,12);(14,16);(15,19);(16,24);(17,22);(18,11);(19,21);(20
        ,33);(21,34);(22,35);(23,31);(24,46);(25,27);(26,46);(27,42);(28,53);(29,51);(30,39);(31,29);(32,44);(33,34);(34,41);(35,26);
        (36,31);(37,23);(38,23);(39,18);(40,18);(41,20);(42,13);(43,11);(44,11);(45,5);(46,4);(47,1);(48,6);(49,4);(50,5);(52,2);(55,
        1);(57,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(18,1);(19,3);(20,7);(21,8);(22,9);(23,23);(24,31);(25,30);(26,53);(27,44);(28,48);(29,56);(30,70);(31,75);(32,70);(33,62);(
        34,85);(35,61);(36,61);(37,54);(38,36);(39,29);(40,21);(41,22);(42,12);(43,11);(44,9);(45,3);(46,2);(47,3);(51,1)]

        real	0m37.488s
        user	0m23.202s
        sys	0m0.308s

  * To give statistical variation a little rein, I use a ridiculously short message and 1 &sigma;. Alice provokes a large number of repetitions but Eve many more repetitions than trials. Bob should spot her, though Alice probably wouldn't: her histogram is silly but then so is Bob's.

        length of message? 3
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 1
        number of trials? 1000

        7 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 1845 repetitions (Alice-Eve); 4070 repetitions (Eve-Bob);
        average check bits (Alice/Eve) 0.80; minimum check bits (Alice/Eve) 0; average check bits (Eve/Bob) 0.74; minimum check bits
        (Eve/Bob) 0
        histogram of check-bit lengths (Alice/Eve) [(0,467);(1,322);(2,161);(3,44);(4,6)]
        histogram of check-bit lengths (Eve/Bob) [(0,445);(1,394);(2,139);(3,22)]

        real	0m20.339s
        user	0m4.077s
        sys	0m0.076s

        real	0m25.204s
        user	0m1.680s
        sys	0m0.038s
  

_Definitely_ no cigar.

<a name="superEve"></a>
## Alice, Bob and cleverer Eve

In the simulation I can make Alice careful or careless. In reality she will be careful, generating far more code bits than she is likely to need. If she were careless or deliberately generated too few, she'd have to restart the communication, using the same hash keys twice, and that's a security risk. So Eve shouldn't worry: just let Alice control things. Play Bob to Alice and Alice to Bob, confident that in either direction there will be plenty of code bits to deal with the *M* that Alice has in mind, or if not, a restart won't be totally unexpected.

So cleverer Eve doesn't fake a mask when dealing with Alice: instead she does exactly what Bob would do, selecting check bits with probability 1/4. And when dealing with Bob she's just another Alice, agreeing a code as he directs. There is a possibility, if Alice is deliberately careless, that sometimes Alice could agree enough code bits with Eve to encrypt *M* when Eve and Bob did not. In that case Eve would have to ask Bob to restart. But also in that case Alice would be likely to provoke restarts of her own. 

As a bonus, this Eve is easier to code. No faking, no irrational restarts, two internal parallel processes.

The command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                superEve.qtp LogEve.qtp SystemAEB.qtp)

  * With cautious Alice and a long message, no restarts and Eve hides perfectly -- and note that she's perfectly tagging her classical messages. Her histogram is a bit wider than Alice's, but it's within normal limits because she is exactly playing Bob.
  
        length of message? 1000
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 1000

        4351 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); average
        check bits (Alice/Eve) 544.96; minimum check bits (Alice/Eve) 472; average check bits (Eve/Bob) 543.49; minimum check bits
        (Eve/Bob) 479
        histogram of check-bit lengths (Alice/Eve)
        [(472,1);(478,1);(481,2);(482,1);(485,1);(487,1);(492,1);(493,2);(495,2);(497,1);(498,2);(499,1);(501,1);(502,3);(503,1);(504
        ,5);(505,1);(506,2);(507,4);(508,3);(509,4);(510,1);(511,2);(512,11);(513,8);(514,7);(515,7);(516,3);(517,11);(518,9);(519,7)
        ;(520,10);(521,5);(522,16);(523,9);(524,14);(525,11);(526,15);(527,14);(528,11);(529,24);(530,17);(531,17);(532,17);(533,13);
        (534,14);(535,20);(536,20);(537,17);(538,10);(539,19);(540,22);(541,16);(542,22);(543,11);(544,27);(545,23);(546,21);(547,28)
        ;(548,18);(549,19);(550,19);(551,16);(552,10);(553,15);(554,17);(555,14);(556,13);(557,14);(558,16);(559,11);(560,15);(561,14
        );(562,9);(563,7);(564,12);(565,13);(566,16);(567,16);(568,14);(569,10);(570,7);(571,8);(572,6);(573,6);(574,7);(575,8);(576,
        7);(577,3);(578,8);(579,8);(580,6);(581,5);(582,4);(583,3);(584,8);(585,6);(586,4);(587,2);(588,1);(589,2);(590,2);(592,1);(
        593,2);(594,2);(596,1);(598,1);(600,1);(601,1);(603,1);(604,1);(613,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(479,1);(483,1);(485,2);(487,2);(489,1);(490,1);(492,2);(493,2);(494,1);(495,1);(496,1);(497,2);(498,2);(499,1);(500,5);(501
        ,2);(502,1);(503,4);(504,2);(505,4);(506,4);(507,5);(508,5);(509,4);(510,5);(511,7);(512,8);(513,4);(514,10);(515,10);(516,10
        );(517,10);(518,5);(519,9);(520,17);(521,6);(522,21);(523,12);(524,6);(525,14);(526,12);(527,11);(528,10);(529,20);(530,18);(
        531,12);(532,14);(533,14);(534,16);(535,30);(536,20);(537,12);(538,21);(539,19);(540,16);(541,15);(542,21);(543,14);(544,20);
        (545,17);(546,28);(547,18);(548,16);(549,15);(550,17);(551,9);(552,16);(553,15);(554,23);(555,18);(556,15);(557,16);(558,12);
        (559,15);(560,11);(561,20);(562,7);(563,15);(564,16);(565,7);(566,12);(567,8);(568,11);(569,3);(570,4);(571,7);(572,5);(573,6
        );(574,1);(575,6);(576,11);(577,6);(578,6);(579,5);(580,6);(581,1);(582,2);(583,2);(584,5);(585,5);(586,3);(587,1);(588,1);(
        589,2);(590,5);(591,4);(592,1);(593,2);(594,1);(595,4);(596,2);(597,3);(598,1);(599,1);(602,2);(603,1);(604,1);(613,1);(616,1
        )]

        real	4m19.091s
        user	3m49.538s
        sys	0m2.410s

  * With careless Alice (not enough qbits) and a shorter message Eve is still under cover: no more Bob restarts from her than Eve restarts from Alice. This time her histogram's a tiny bit narrower, but all within normal variation.

        length of message? 100
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        266 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 952 repetitions (Alice-Eve); 950 repetitions (Eve-Bob);
        average check bits (Alice/Eve) 32.07; minimum check bits (Alice/Eve) 17; average check bits (Eve/Bob) 32.06; minimum check
        bits (Eve/Bob) 18
        histogram of check-bit lengths (Alice/Eve)
        [(17,1);(18,3);(19,2);(20,2);(21,5);(22,6);(23,22);(24,21);(25,40);(26,32);(27,53);(28,65);(29,57);(30,79);(31,68);(32,70);(
        33,81);(34,84);(35,62);(36,66);(37,48);(38,45);(39,16);(40,18);(41,15);(42,14);(43,13);(44,3);(45,3);(46,2);(47,2);(48,2)]
        histogram of check-bit lengths (Eve/Bob)
        [(18,3);(19,2);(20,6);(21,7);(22,9);(23,12);(24,30);(25,31);(26,40);(27,46);(28,66);(29,65);(30,69);(31,77);(32,80);(33,76);(
        34,74);(35,53);(36,53);(37,55);(38,42);(39,35);(40,17);(41,17);(42,7);(43,11);(44,8);(45,2);(46,2);(47,2);(48,1);(49,1);(50,1
        )]

        real	0m48.319s
        user	0m24.054s
        sys	0m0.313s
        
  * With a ridiculously short message the same pattern: no more restarts for Bob than he should expect.
  
        length of message? 3
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 1
        number of trials? 1000

        16 qbits per trial
            all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 31 repetitions (Alice-Eve); 19 repetitions (Eve-Bob); average
            check bits (Alice/Eve) 1.97; minimum check bits (Alice/Eve) 0; average check bits (Eve/Bob) 1.97; minimum check bits
            (Eve/Bob) 0
        histogram of check-bit lengths (Alice/Eve) [(0,100);(1,272);(2,334);(3,178);(4,84);(5,29);(6,2);(7,1)]
        histogram of check-bit lengths (Eve/Bob) [(0,122);(1,275);(2,294);(3,184);(4,85);(5,31);(6,6);(7,3)]

        real	0m21.656s
        user	0m1.791s
        sys	0m0.036s
        
So cleverer Eve seems to have got away with it. With the checks that are described in BB84 she's invisible, given the very large initial assumption that she has prior knowledge of Alice and Bob's initial one-time hash keys.

<a name="notreally"></a>
## Or maybe not ... but wait a minute

Restarts are part of the simulation because I wanted to watch the statistical variation of the choice mechanisms. They wouldn't be part of a real implementation, because a restart exposes the one-time hash keys more than once. So Alice would go for a large number of &sigma;s, long hash keys and a large minimum number of checkbits, and things would work out as in the first cleverer Eve test above: that is, she would hide perfectly. It looks as if there is a security hole.

But Alice has programmers for friends. They tell her to try to smoke Eve out. Every now and then she should send a message as long as _all_ her code bits (less the ones she needs to refresh the hash keys). If she's connected directly to Bob he won't stumble, because he will have the same number of code bits as she does. But if Eve is in the way then she is in trouble: she probably won't have agreed the same number of code bits with Bob as Alice has agreed with her. So she can either send Bob a different message or run away.

I've simulated this defence. Every four messages or so, choosing at random, Alice sees if she has more than the expected number *n*/2-*n*/8-5*w* of secret code bits. If so, she makes up a random message of the same length as her code-bit sequence and fires it at whoever is listening on the quantum channel. If it's Eve she has a small chance of having as many or more code bits, but that's not enough for a long life.

The command is

        (cd examples/BB84_QKD; time ../../Qtpi nr_Alice.qtp nr_Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                    nr_superEve.qtp LogEve.qtp SystemAEB.qtp)

  * The logging process plays the r&ocirc;le of the Zurich park. If the message that Bob logged is not the one that Alice logged, and neither of them logged quantum or classical interference, then it's an 'undetected corrupt message'. Alice should fire at Eve about 1/8 of the time, and Eve can only duck a small proportion. 116 hits out of about 125 shots: it seems that Eve is no longer undectable.
  
        length of message? 1000
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 1000

        4589 qbits per trial
        all done: 865 Eve's; 0 Alice's; 135 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); average
        check bits (Alice/Eve) 573.10; minimum check bits (Alice/Eve) 495; average check bits (Eve/Bob) 574.45; minimum check bits
        (Eve/Bob) 496
        histogram of check-bit lengths (Alice/Eve)
        [(495,1);(496,1);(504,1);(508,1);(515,2);(518,1);(519,1);(520,2);(524,2);(525,1);(526,2);(527,3);(528,3);(529,1);(530,3);(531
        ,2);(533,4);(534,7);(535,6);(536,6);(537,6);(538,3);(539,4);(540,6);(541,7);(542,9);(543,12);(544,6);(545,5);(546,7);(547,10)
        ;(548,7);(549,14);(550,11);(551,17);(552,7);(553,11);(554,17);(555,15);(556,14);(557,15);(558,14);(559,11);(560,11);(561,14);
        (562,19);(563,19);(564,17);(565,18);(566,15);(567,14);(568,15);(569,18);(570,16);(571,20);(572,17);(573,23);(574,26);(575,18)
        ;(576,13);(577,14);(578,11);(579,14);(580,19);(581,13);(582,17);(583,19);(584,18);(585,16);(586,21);(587,11);(588,17);(589,8)
        ;(590,10);(591,9);(592,17);(593,9);(594,12);(595,10);(596,13);(597,7);(598,10);(599,7);(600,15);(601,5);(602,9);(603,9);(604,
        5);(605,3);(606,7);(607,4);(608,6);(609,4);(610,5);(611,6);(612,7);(613,4);(614,4);(615,3);(616,3);(617,4);(618,2);(619,3);(
        620,2);(621,3);(622,2);(623,2);(624,1);(629,2);(630,1);(632,3);(633,1);(638,1);(660,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(496,1);(508,1);(514,1);(516,1);(517,2);(518,2);(521,1);(522,2);(523,1);(524,2);(525,1);(527,1);(528,4);(529,3);(530,2);(531
        ,1);(532,3);(533,5);(534,3);(535,2);(537,4);(538,4);(539,8);(540,4);(541,9);(542,8);(543,4);(544,7);(545,9);(546,10);(547,10)
        ;(548,10);(549,6);(550,12);(551,13);(552,8);(553,14);(554,11);(555,14);(556,14);(557,19);(558,14);(559,12);(560,12);(561,12);
        (562,16);(563,18);(564,17);(565,14);(566,20);(567,20);(568,15);(569,24);(570,20);(571,16);(572,14);(573,20);(574,19);(575,17)
        ;(576,12);(577,16);(578,25);(579,15);(580,16);(581,14);(582,15);(583,14);(584,8);(585,19);(586,17);(587,13);(588,9);(589,11);
        (590,14);(591,15);(592,13);(593,10);(594,11);(595,12);(596,9);(597,8);(598,8);(599,7);(600,9);(601,9);(602,12);(603,7);(604,
        10);(605,10);(606,8);(607,8);(608,5);(609,3);(610,14);(611,6);(612,1);(613,3);(614,4);(615,4);(616,2);(617,4);(618,7);(620,5)
        ;(621,3);(622,2);(624,1);(625,1);(626,2);(627,2);(628,1);(630,2);(633,3);(634,1);(638,1);(639,1);(648,1)]

        real	4m41.219s
        user	4m4.088s
        sys	0m2.542s

But is she *really* detectable? If Alice is sending _real_ messages she'll be using less than all her code bits: the swamping messages will be some kind of fake, made up for the purpose of smoking out Eve. Eve knows how Alice works: she should invent similar swamping messages, send them to Bob at the same frequency as Alice swamps her, and make sure that the _real_ messages all arrive in the right order.  I haven't simulated this counter-counter measure.

If they looked at their own message statistics Bob and Alice would be unaware of Eve's presence: Bob will see swamping messages as often as he'd expect, and Alice will see a normal histogram of checkbit lengths. If they look at message logs Eve will be unmasked because the log of checkbit masks and lengths won't match, and nor will the occurrences of swamping messages. 

It seems likely that anything Alice can do online can be matched by Eve. So perhaps there isn't a realistic defence, unless there is a channel outside the protocol for comparing logs.

<a name="whataboutit"></a>
## But does the attack work in any implementations?

If an implementation of the protocol is careless about the secrecy of the initial hash keys, an Eve could be successful. If it is careless with secrecy in dealing with recovery from hardware crashes, then one could imagine that an Eve-collaborator could provoke Bob or Alice to crash and allow an Eve to intervene. I should like to look at implementations to see if it's possible. If an attack is effective then, of course, it would provoke greater secrecy in future implementations. Which wouldn't be a bad thing.

<a name="codswallop"></a>
## Oh no it isn't

BB84 QKD is designed to daisy-chain A&harr;B, B&harr;C, ... Y&harr;Z. Breaking one of the links and inserting a new component, e.g. by making A&harr;E and E&harr;B  is of course possible, provided E knows the secret keys for that link, and can easily be transformed after the first iteration into two links with separate keys. That's how it's supposed to work. The problem is keeping the keys secret. In practice that may not be as difficult as I had thought it was, given privacy amplification techniques (see, for example, Renner and Wolf, _Unconditional Authenticity and Privacy from an Arbitrarily Weak Secret_).

So I was silly. But I'm not going to delete this stuff, though I probably should (and then you could recover it from the commit history or the Wayback Machine).

<a name="whyEve"></a>
## Why "Eve"?

"Eve" from "eavesdropper"? I do hope so. Not, I hope, from any notion of females as deceptive.
