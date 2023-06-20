import "methods/Methods_base.spec";

// check this rule for every change in setup to make sure all is reachable 
use builtin rule sanity;


/* 
    Property: claiming reward twice is equivalent to one claim reward 

    Note : this rule is implemented by comparing the whole storage 

*/


rule noDoubleClaim() {

    env e; 
    //arbitrary array of any length (might be constrained due to loop unrolling )
    address[] assets; 
    uint256 l = assets.length;
    address to;
    claimAllRewards(e, assets, to);
    storage afterFirst = lastStorage;
    claimAllRewards(e, assets, to);
    storage afterSecond = lastStorage;

    assert afterSecond == afterFirst;
}

rule onlyAuthorizeCanDecrease(method f) {

    address user; address reward;
    uint256 before = getUserAccruedRewards(user, reward);

    env e;
    calldataarg args;
    f(e,args);

    uint256 after = getUserAccruedRewards(user, reward);

    assert after < before => getClaimer(user) == e.msg.sender; 
}


