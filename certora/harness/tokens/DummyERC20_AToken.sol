// SPDX-License-Identifier: MIT
pragma solidity ^0.8.10;
import "./DummyERC20Impl.sol";

contract DummyERC20_AToken is DummyERC20Impl {
    function scaledTotalSupply() public view returns (uint256) {
        return t;
    }

    function scaledBalanceOf(address account) public view returns (uint256) {
        return b[account];
    }

    function getScaledUserBalanceAndSupply(address account) public view returns (uint256, uint256){
        return (scaledBalanceOf(account), scaledTotalSupply());
    }
}
