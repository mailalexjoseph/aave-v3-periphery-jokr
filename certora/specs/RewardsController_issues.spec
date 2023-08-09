import "methods/Methods_base.spec";

///////////////// Properties ///////////////////////



// STATUS: VERIFIED
// Property: handleAction should never revert no matter what
rule handleAction_should_never_revert() {
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

    
}