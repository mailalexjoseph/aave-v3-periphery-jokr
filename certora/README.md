


### Certora Verification Setup

use default.conf as a starting point. It is a simpler configuration and should be used to make sure the rule is proven first on a simplified version of the code.

verifyRewardsController.conf should be used to check for better coverage. it contains:
1. more loop unrolling
2. more erc20 and  multi-reward token |(?) 