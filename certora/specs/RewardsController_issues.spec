import "methods/Methods_base.spec";

///////////////// Properties ///////////////////////


// STATUS: VIOLATED
// Property: handleAction should never revert no matter what
// handleAction function got reverted when the reward index overflows and 
//      
rule handleAction_should_never_revert(method f) {
    env e;
    address user1;
    uint256 totalSupply1;
    uint256 userBalance1;

    handleAction@withrevert(e,user1,totalSupply1,userBalance1);
    bool firstReverted = lastReverted;
    
    calldataarg args;

    f(e,args);

    address user2;
    uint256 totalSupply2;
    uint256 userBalance2;

    handleAction@withrevert(e,user2,totalSupply2,userBalance2);
    bool secondReverted = lastReverted;

    assert !firstReverted => !secondReverted,
        "handleAction should never revert";
    
}


// STATUS: VERIFIED
// Property: user rewards should never decrease unless claimed
// rule rewards_should_never_decrease_unless_claimed(){
//     env e;
//     method f;
//     calldataarg args;

//     address asset;
//     require getAssetDecimals(asset) == 6;

//     address[] assets;
//     address user;
//     address reward;

//     uint _rewards = getUserRewards(e,assets,user,reward);
 
//     f(e,args);

//     uint rewards_ = getUserRewards(e,assets,user,reward);

//     assert !claimMethods(f) => rewards_ >= _rewards,
//         "user rewards should not decrease unless claimed";


// }

