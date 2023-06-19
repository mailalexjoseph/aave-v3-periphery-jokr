import "./ERC20_methods.spec";

using DummyERC20_AToken as AToken;

methods {
    function _.getScaledUserBalanceAndSupply(address) external => DISPATCHER(true);
    function _.scaledTotalSupply() external => DISPATCHER(true);
    function _.performTransfer(address, address, uint256) external => DISPATCHER(true);
    function _.latestAnswer() external => NONDET;
}